#![allow(unused)]

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::mem;

use rustc_ast::visit::Visitor;
use rustc_ast::{Crate, EnumDef, ast, visit};
use rustc_data_structures::fx::FxHashSet;
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

impl Resolver<'_, '_> {
    fn nearest_normal_mod(&self, def_id: LocalDefId) -> LocalDefId {
        self.get_nearest_non_block_module(def_id.to_def_id()).nearest_parent_mod().expect_local()
    }

    fn private_vis_import(&self, decl: Decl<'_>) -> Visibility {
        let DeclKind::Import { import, .. } = decl.kind else { unreachable!() };
        Visibility::Restricted(
            import
                .id()
                .map(|id| self.nearest_normal_mod(self.local_def_id(id)))
                .unwrap_or(CRATE_DEF_ID),
        )
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
    def_effective_visibilities: EffectiveVisibilities,
    /// While walking import chains we need to track effective visibilities per-decl, and def id
    /// keys in `Resolver::effective_visibilities` are not enough for that, because multiple
    /// declarations can correspond to a single def id in imports. So we keep a separate table.
    import_effective_visibilities: EffectiveVisibilities<Decl<'ra>>,
    /// Priority queue for bindings.
    heap: BinaryHeap<UpdateStep<'ra, 'tcx>>,
    visited: FxHashSet<Decl<'ra>>,
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

    pub(crate) fn compute_effective_visibilities<'c>(
        r: &'a mut Resolver<'ra, 'tcx>,
        krate: &'c Crate,
    ) -> FxHashSet<Decl<'ra>> {
        let mut collector = EffectiveVisibilitiesVisitor::new(r);

        // Step 0: Initialize heap with crate bindings.
        collector.def_effective_visibilities.update_root();
        collector.collect_module_bindings(CRATE_DEF_ID);

        // Step 1: iterate over bindings.
        while let Some(UpdateStep { parent_mod, binding, tcx: _ }) = collector.heap.pop() {
            if collector.visited.contains(&binding) {
                continue;
            }

            // Step 1.1: update effective visibility of the binding.
            // TODO: we need to check for update and insert back to queue with lower cost? Cost in that case
            // have to contain effective vis also?
            collector.update_binding_effective_visibility(parent_mod, binding);

            // Step 1.2: put new elements in the heap.
            if let Res::Def(DefKind::Mod | DefKind::Enum | DefKind::Trait, module_id) =
                binding.res()
                && let Some(module_id) = module_id.as_local()
            {
                collector.collect_module_bindings(module_id);
            }

            collector.visited.insert(binding);
        }

        // Step 2: Update effective visibilities for adt's fields. TODO: because we can't check
        // them during modules traverse.
        visit::walk_crate(&mut collector, krate);

        collector.r.effective_visibilities = collector.def_effective_visibilities;

        let mut exported_ambiguities = FxHashSet::default();

        // Step 3: Update visibilities for import def ids. These are not used during the
        // `EffectiveVisibilitiesVisitor` pass, because we have more detailed declaration-based
        // information, but are used by later passes. Effective visibility of an import def id
        // is the maximum value among visibilities of declarations corresponding to that def id.
        for (decl, eff_vis) in collector.import_effective_visibilities.iter() {
            let DeclKind::Import { import, .. } = decl.kind else { unreachable!() };
            if let Some(node_id) = import.id() {
                r.effective_visibilities.update_eff_vis(r.local_def_id(node_id), eff_vis, r.tcx);
            }
            if decl.ambiguity.get().is_some() && eff_vis.is_public_at_level(Level::Reexported) {
                exported_ambiguities.insert(*decl);
            }
        }

        info!("resolve::effective_visibilities: {:#?}", r.effective_visibilities);

        exported_ambiguities
    }

    fn collect_module_bindings(&mut self, module_id: LocalDefId) {
        let module = self.r.expect_module(module_id.to_def_id());
        for (_, name_resolution) in self.r.resolutions(module).borrow().iter() {
            let Some(decl) = name_resolution.borrow().best_decl() else {
                continue;
            };

            let state = UpdateStep::new(self.r.tcx, module_id, decl);
            self.heap.push(state);
        }
    }

    fn update_field(&mut self, def_id: LocalDefId, parent_id: LocalDefId) {
        self.update_def(def_id, self.r.tcx.local_visibility(def_id), ParentId::Def(parent_id));
    }

    fn update_binding_effective_visibility(&mut self, parent_mod: LocalDefId, mut decl: Decl<'ra>) {
        let mut parent_id = ParentId::Def(parent_mod);
        while let DeclKind::Import { source_decl, import } = decl.kind {
            self.update_import(decl, parent_id);
            parent_id = ParentId::Import(decl);
            decl = source_decl;
        }

        if let Some(def_id) = decl.res().opt_def_id().and_then(|id| id.as_local()) {
            self.update_def(def_id, decl.vis().expect_local(), parent_id);
        }
    }

    fn update_import(&mut self, decl: Decl<'ra>, parent_id: ParentId<'ra>) {
        let nominal_vis = decl.vis().expect_local();
        let inherited_eff_vis = self.effective_vis_or_private(parent_id);
        let tcx = self.r.tcx;
        let changed = self.import_effective_visibilities.update(
            decl,
            Some(nominal_vis),
            || self.r.private_vis_import(decl),
            inherited_eff_vis,
            parent_id.level(),
            tcx,
        );
    }

    fn update_def(
        &mut self,
        def_id: LocalDefId,
        nominal_vis: Visibility,
        parent_id: ParentId<'ra>,
    ) {
        let inherited_eff_vis = self.effective_vis_or_private(parent_id);
        let tcx = self.r.tcx;
        let changed = self.def_effective_visibilities.update(
            def_id,
            Some(nominal_vis),
            || self.r.private_vis_def(def_id),
            inherited_eff_vis,
            parent_id.level(),
            tcx,
        );
    }

    fn effective_vis_or_private(&mut self, parent_id: ParentId<'ra>) -> EffectiveVisibility {
        // Private nodes are only added to the table for caching, they could be added or removed at
        // any moment without consequences, so we don't set `changed` to true when adding them.
        *match parent_id {
            ParentId::Def(def_id) => self
                .def_effective_visibilities
                .effective_vis_or_private(def_id, || self.r.private_vis_def(def_id)),
            ParentId::Import(binding) => self
                .import_effective_visibilities
                .effective_vis_or_private(binding, || self.r.private_vis_import(binding)),
        }
    }
}

impl<'a, 'ra, 'tcx> Visitor<'a> for EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    fn visit_item(&mut self, item: &'a ast::Item) {
        let def_id = self.r.local_def_id(item.id);
        // Update effective visibilities of adt fields.
        // If it's a mod, also make the visitor walk all of its items
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
