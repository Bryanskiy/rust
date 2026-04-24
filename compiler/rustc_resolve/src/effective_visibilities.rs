#![allow(unused)]
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::mem;
use std::ops::{Index, IndexMut};

use indexmap::map::Entry;
use rustc_ast::visit::Visitor;
use rustc_ast::{Crate, EnumDef, ast, visit};
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CRATE_DEF_ID, DefId, LocalDefId};
use rustc_middle::middle::privacy::{EffectiveVisibilities, EffectiveVisibility, Level};
use rustc_middle::ty::{TyCtxt, Visibility};
use tracing::info;

use crate::{Decl, DeclKind, Res, Resolver};

#[derive(Clone, Copy)]
enum ParentId<'ra> {
    Def(LocalDefId),
    Import(Decl<'ra>),
}

impl ParentId<'_> {
    fn level(self) -> Level {
        match self {
            ParentId::Def(_) => Level::Direct,
            ParentId::Import(_) => Level::Reexported,
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct PartialEffectiveVis {
    direct: Visibility,
    reexported: Visibility,
    is_reexported: bool,
}

impl Default for PartialEffectiveVis {
    fn default() -> PartialEffectiveVis {
        PartialEffectiveVis::from_vis(Visibility::Public)
    }
}

impl PartialEffectiveVis {
    fn to_effective_vis(self) -> EffectiveVisibility {
        let reexported = if self.is_reexported { self.reexported } else { self.direct };
        EffectiveVisibility::from_parts(self.direct, reexported, reexported, reexported)
    }

    fn set_at_level(&mut self, vis: Visibility, level: Level) {
        match level {
            Level::Direct => self.direct = vis,
            Level::Reexported => {
                self.reexported = vis;
                self.is_reexported = true;
            }
            _ => unreachable!(),
        }
    }

    const fn from_vis(vis: Visibility) -> PartialEffectiveVis {
        PartialEffectiveVis { direct: vis, reexported: vis, is_reexported: false }
    }
}

#[derive(Copy, Clone)]
struct UpdateStep<'ra, 'tcx> {
    parent_mod: LocalDefId,
    binding: Decl<'ra>,
    tcx: TyCtxt<'tcx>,
}

impl<'ra, 'tcx> PartialEq for UpdateStep<'ra, 'tcx> {
    fn eq(&self, other: &Self) -> bool {
        self.binding.eq(&other.binding)
    }
}

impl<'ra, 'tcx> Eq for UpdateStep<'ra, 'tcx> {}

impl<'ra, 'tcx> Ord for UpdateStep<'ra, 'tcx> {
    fn cmp(&self, other: &Self) -> Ordering {
        // FIXME: remove?
        if self.binding.vis() == other.binding.vis() {
            return Ordering::Equal;
        }

        if self.binding.vis().is_at_least(other.binding.vis(), self.tcx) {
            Ordering::Greater
        } else {
            Ordering::Less
        }
    }
}

impl<'ra, 'tcx> PartialOrd for UpdateStep<'ra, 'tcx> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'ra, 'tcx> UpdateStep<'ra, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, parent_mod: LocalDefId, binding: Decl<'ra>) -> UpdateStep<'ra, 'tcx> {
        UpdateStep { tcx, parent_mod, binding }
    }
}

pub(crate) struct EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    r: &'a mut Resolver<'ra, 'tcx>,
    def_effective_visibilities: FxIndexMap<LocalDefId, PartialEffectiveVis>,
    /// While walking import chains we need to track effective visibilities per-decl, and def id
    /// keys in `Resolver::effective_visibilities` are not enough for that, because multiple
    /// declarations can correspond to a single def id in imports. So we keep a separate table.
    import_effective_visibilities: FxIndexMap<Decl<'ra>, PartialEffectiveVis>,
    /// Priority queue for bindings.
    heap: BinaryHeap<UpdateStep<'ra, 'tcx>>,
    visited: FxHashSet<Decl<'ra>>,
}

impl Resolver<'_, '_> {
    fn nearest_normal_mod(&self, def_id: LocalDefId) -> LocalDefId {
        self.get_nearest_non_block_module(def_id.to_def_id()).nearest_parent_mod().expect_local()
    }

    fn private_vis_def(&self, def_id: LocalDefId) -> Visibility {
        // For mod items `nearest_normal_mod` returns its argument, but we actually need its parent.
        let normal_mod_id = self.nearest_normal_mod(def_id);
        if normal_mod_id == def_id {
            Visibility::Restricted(self.tcx.local_parent(def_id))
        } else {
            Visibility::Restricted(normal_mod_id)
        }
    }
}

impl<'a, 'ra, 'tcx> EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    fn new(r: &'a mut Resolver<'ra, 'tcx>) -> EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
        EffectiveVisibilitiesVisitor {
            r,
            def_effective_visibilities: Default::default(),
            import_effective_visibilities: Default::default(),
            heap: Default::default(),
            visited: Default::default(),
        }
    }

    /// Fills the `Resolver::effective_visibilities` table with public & exported items
    /// For now, this doesn't resolve macros (FIXME) and cannot resolve Impl, as we
    /// need access to a `TyCtxt` for that. Returns the set of ambiguous re-exports.
    pub(crate) fn compute_effective_visibilities<'c>(
        r: &'a mut Resolver<'ra, 'tcx>,
        krate: &'c Crate,
    ) -> FxHashSet<Decl<'ra>> {
        let mut collector = EffectiveVisibilitiesVisitor::new(r);

        // Step 0: Initialize heap with crate bindings.
        collector.update_root();
        collector.collect_module_bindings(CRATE_DEF_ID);

        // Step 1: iterate over bindings.
        while let Some(UpdateStep { parent_mod, binding, tcx: _ }) = collector.heap.pop() {
            // TODO: do not visit before parent module
            if collector.visited.contains(&binding) {
                continue;
            }

            // Step 1.1: update effective visibility of the binding.
            collector.update_binding(parent_mod, binding);

            // Step 1.2: put new elements in the heap.
            if !binding.is_import()
                && let Res::Def(DefKind::Mod | DefKind::Enum | DefKind::Trait, module_id) =
                    binding.res()
                && let Some(module_id) = module_id.as_local()
            {
                collector.collect_module_bindings(module_id);
            }

            collector.visited.insert(binding);
        }

        visit::walk_crate(&mut collector, krate);

        let mut effective_visibilities = EffectiveVisibilities::default();
        for (id, partial_eff_vis) in collector.def_effective_visibilities.iter() {
            // println!("id: {:?}", id);
            // println!("partial_eff_vis: {:?}", partial_eff_vis);
            effective_visibilities.insert(*id, partial_eff_vis.to_effective_vis());
        }

        let mut exported_ambiguities = FxHashSet::default();

        // Step 2: Update visibilities for import def ids. These are not used during the
        // `EffectiveVisibilitiesVisitor` pass, because we have more detailed declaration-based
        // information, but are used by later passes. Effective visibility of an import def id
        // is the maximum value among visibilities of declarations corresponding to that def id.
        for (decl, partial_eff_vis) in collector.import_effective_visibilities.iter() {
            let DeclKind::Import { import, .. } = decl.kind else { unreachable!() };
            let effective_vis = partial_eff_vis.to_effective_vis();
            if let Some(node_id) = import.id() {
                effective_visibilities.update_eff_vis(
                    r.local_def_id(node_id),
                    &effective_vis,
                    r.tcx,
                );
            }
            if decl.ambiguity.get().is_some() && effective_vis.is_public_at_level(Level::Reexported)
            {
                exported_ambiguities.insert(*decl);
            }
        }

        // Step 3: Update effective visibilities for adt's fields. TODO: because we can't check
        // them during modules traverse.
        // visit::walk_crate(&mut collector, krate);
        r.effective_visibilities = effective_visibilities;

        info!("resolve::effective_visibilities: {:#?}", r.effective_visibilities);

        exported_ambiguities
    }

    fn update_root(&mut self) {
        self.def_effective_visibilities
            .insert(CRATE_DEF_ID, PartialEffectiveVis::from_vis(Visibility::Public));
    }

    fn collect_module_bindings(&mut self, module_id: LocalDefId) {
        let module = self.r.expect_module(module_id.to_def_id());
        println!("collect module bindings: {:?}", module.span);
        for (_, name_resolution) in self.r.resolutions(module).borrow().iter() {
            let Some(decl) = name_resolution.borrow().best_decl() else {
                continue;
            };

            println!("add decl: {:?}, parent: {:?}", decl.span, module_id);
            let state = UpdateStep::new(self.r.tcx, module_id, decl);
            self.heap.push(state);
        }
    }

    fn update_field(&mut self, def_id: LocalDefId, parent_id: LocalDefId) {
        self.update_def(def_id, self.r.tcx.local_visibility(def_id), ParentId::Def(parent_id));
    }

    fn update_binding(&mut self, parent_mod: LocalDefId, mut decl: Decl<'ra>) {
        println!("update binding: {:?}", decl.span);

        let mut parent_id = ParentId::Def(parent_mod);

        // Walk through re‑export chains.
        while let DeclKind::Import { source_decl, import } = decl.kind {
            self.update_import(decl, parent_id);
            parent_id = ParentId::Import(decl);
            decl = source_decl;
        }

        // Update the definition at the end of the chain.
        if let Some(def_id) = decl.res().opt_def_id().and_then(|id| id.as_local()) {
            self.update_def(def_id, decl.vis().expect_local(), parent_id);
        }
    }

    fn update_import(&mut self, decl: Decl<'ra>, parent_id: ParentId<'ra>) {
        // TODO: default in parent. NV restrict based on level
        let nominal_vis = decl.vis().expect_local();
        let inherited_vis = self.inherit_vis_from_parent(nominal_vis, parent_id);
        let entry = self
            .import_effective_visibilities
            .entry(decl)
            .or_insert_with(PartialEffectiveVis::default);

        println!("update_import before: {:?}", entry);

        entry.set_at_level(inherited_vis, parent_id.level());
        println!("update_import after: {:?}", entry);
    }

    fn update_def(
        &mut self,
        def_id: LocalDefId,
        nominal_vis: Visibility,
        parent_id: ParentId<'ra>,
    ) {
        let inherited_vis = self.inherit_vis_from_parent(nominal_vis, parent_id);
        let entry = self
            .def_effective_visibilities
            .entry(def_id)
            .or_insert_with(PartialEffectiveVis::default);

        println!("update_def before: {:?}", entry);
        println!("update_def inherited_vis: {:?}", inherited_vis);
        entry.set_at_level(inherited_vis, parent_id.level());
        println!("update_def after: {:?}", entry);
    }

    fn inherit_vis_from_parent(&self, nominal_vis: Visibility, id: ParentId<'ra>) -> Visibility {
        let new_vis = match id {
            ParentId::Def(def_id) => self.def_effective_visibilities.index(&def_id).direct,
            ParentId::Import(binding) => {
                self.import_effective_visibilities.index(&binding).reexported
            }
        };
        new_vis.min(nominal_vis, self.r.tcx)
    }
}

impl<'a, 'ra, 'tcx> Visitor<'a> for EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    fn visit_item(&mut self, item: &'a ast::Item) {
        let def_id = self.r.local_def_id(item.id);
        // Update effective visibilities of adt fields.
        match item.kind {
            ast::ItemKind::Mod(..) => {
                visit::walk_item(self, item);
            }

            ast::ItemKind::Enum(_, _, EnumDef { ref variants }) => {
                for variant in variants {
                    let variant_def_id = self.r.local_def_id(variant.id);
                    for field in variant.data.fields() {
                        self.update_field(self.r.local_def_id(field.id), variant_def_id);
                    }
                }
            }

            ast::ItemKind::Struct(_, _, ref def) | ast::ItemKind::Union(_, _, ref def) => {
                for field in def.fields() {
                    self.update_field(self.r.local_def_id(field.id), def_id);
                }
            }

            // Should be unreachable at this stage
            ast::ItemKind::MacCall(..) | ast::ItemKind::DelegationMac(..) => panic!(
                "ast::ItemKind::MacCall encountered, this should not anymore appear at this stage"
            ),

            ast::ItemKind::ExternCrate(..)
            | ast::ItemKind::Use(..)
            | ast::ItemKind::Static(..)
            | ast::ItemKind::Const(..)
            | ast::ItemKind::ConstBlock(..)
            | ast::ItemKind::GlobalAsm(..)
            | ast::ItemKind::TyAlias(..)
            | ast::ItemKind::Trait(..)
            | ast::ItemKind::TraitAlias(..)
            | ast::ItemKind::MacroDef(..)
            | ast::ItemKind::ForeignMod(..)
            | ast::ItemKind::Fn(..)
            | ast::ItemKind::Delegation(..)
            // Resolved in rustc_privacy when types are available
            | ast::ItemKind::Impl(..) => return,
        }
    }
}
