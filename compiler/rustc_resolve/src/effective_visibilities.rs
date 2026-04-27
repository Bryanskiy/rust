#![allow(unused)]

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::mem;
use std::ops::Index;

use rustc_ast::visit::Visitor;
use rustc_ast::{Crate, EnumDef, ast, visit};
use rustc_data_structures::fx::{FxHashSet, FxIndexMap};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CRATE_DEF_ID, LocalDefId};
use rustc_middle::middle::privacy::{EffectiveVisibility, Level};
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
}

impl PartialEffectiveVis {
    fn to_effective_vis(self) -> EffectiveVisibility {
        EffectiveVisibility::from_parts(
            self.direct,
            self.reexported,
            self.reexported,
            self.reexported,
        )
    }

    fn min<'tcx>(self, other: PartialEffectiveVis, tcx: TyCtxt<'tcx>) -> PartialEffectiveVis {
        PartialEffectiveVis {
            direct: self.direct.min(other.direct, tcx),
            reexported: self.reexported.min(other.reexported, tcx),
        }
    }

    const fn from_vis(vis: Visibility) -> PartialEffectiveVis {
        PartialEffectiveVis { direct: vis, reexported: vis }
    }
}

pub(crate) struct EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    r: &'a mut Resolver<'ra, 'tcx>,
    def_effective_visibilities: FxIndexMap<LocalDefId, PartialEffectiveVis>,
    /// While walking import chains we need to track effective visibilities per-decl, and def id
    /// keys in `Resolver::effective_visibilities` are not enough for that, because multiple
    /// declarations can correspond to a single def id in imports. So we keep a separate table.
    import_effective_visibilities: FxIndexMap<Decl<'ra>, PartialEffectiveVis>,
    // It's possible to recalculate this at any point, but it's relatively expensive.
    current_private_vis: Visibility,
    /// Priority queue for bindings. They are processed in descending order of nominal
    /// visibility (most public first). This ensures that when we visit a binding,
    /// we have already computed the maximum possible effective visibility of its parent module
    /// including possible reexports. As a result, we can calculate effective visibility of
    /// a binding without needing to revisit nodes.
    heap: BinaryHeap<UpdateStep<'ra, 'tcx>>,
    visited: FxHashSet<Decl<'ra>>,
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
            if def_id == CRATE_DEF_ID {
                return Visibility::Public;
            }
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

impl<'a, 'ra, 'tcx> EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    /// Fills the `Resolver::effective_visibilities` table with public & exported items
    /// For now, this doesn't resolve macros (FIXME) and cannot resolve Impl, as we
    /// need access to a TyCtxt for that. Returns the set of ambiguous re-exports.
    pub(crate) fn compute_effective_visibilities<'c>(
        r: &'a mut Resolver<'ra, 'tcx>,
        krate: &'c Crate,
    ) -> FxHashSet<Decl<'ra>> {
        let mut visitor = EffectiveVisibilitiesVisitor {
            r,
            def_effective_visibilities: Default::default(),
            import_effective_visibilities: Default::default(),
            heap: Default::default(),
            visited: Default::default(),
            current_private_vis: Visibility::Restricted(CRATE_DEF_ID),
        };

        visitor.update_root();
        visitor.collect_module_bindings(CRATE_DEF_ID);

        while let Some(UpdateStep { parent_mod, binding, tcx: _ }) = visitor.heap.pop() {
            if visitor.visited.contains(&binding) {
                continue;
            }

            visitor.current_private_vis = Visibility::Restricted(parent_mod);
            visitor.update_binding_effective_visibility(parent_mod, binding);

            if !binding.is_import()
                && let Res::Def(DefKind::Mod | DefKind::Enum | DefKind::Trait, module_id) =
                    binding.res()
                && let Some(module_id) = module_id.as_local()
            {
                visitor.collect_module_bindings(module_id);
            }

            visitor.visited.insert(binding);
        }

        // Update effective visibilities of the ADT's fields, since we can't check
        // them during bindings traversal.
        visitor.current_private_vis = Visibility::Restricted(CRATE_DEF_ID);
        visit::walk_crate(&mut visitor, krate);

        for (id, partial_eff_vis) in visitor.def_effective_visibilities.iter() {
            visitor.r.effective_visibilities.insert(*id, partial_eff_vis.to_effective_vis());
        }

        let mut exported_ambiguities = FxHashSet::default();

        // Update visibilities for import def ids. These are not used during the
        // `EffectiveVisibilitiesVisitor` pass, because we have more detailed declaration-based
        // information, but are used by later passes. Effective visibility of an import def id
        // is the maximum value among visibilities of declarations corresponding to that def id.
        for (decl, partial_eff_vis) in visitor.import_effective_visibilities.iter() {
            let DeclKind::Import { import, .. } = decl.kind else { unreachable!() };
            let eff_vis = partial_eff_vis.to_effective_vis();
            if let Some(node_id) = import.id() {
                r.effective_visibilities.update_eff_vis(r.local_def_id(node_id), &eff_vis, r.tcx);
            }
            if decl.ambiguity.get().is_some() && eff_vis.is_public_at_level(Level::Reexported) {
                exported_ambiguities.insert(*decl);
            }
        }

        info!("resolve::effective_visibilities: {:#?}", r.effective_visibilities);

        exported_ambiguities
    }

    fn update_root(&mut self) {
        self.def_effective_visibilities
            .insert(CRATE_DEF_ID, PartialEffectiveVis::from_vis(Visibility::Public));
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

    // fn effective_vis_or_private(&mut self, parent_id: ParentId<'ra>) -> EffectiveVisibility {
    //     // Private nodes are only added to the table for caching, they could be added or removed at
    //     // any moment without consequences, so we don't set `changed` to true when adding them.
    //     *match parent_id {
    //         ParentId::Def(def_id) => self
    //             .def_effective_visibilities
    //             .effective_vis_or_private(def_id, || self.r.private_vis_def(def_id)),
    //         ParentId::Import(binding) => self
    //             .import_effective_visibilities
    //             .effective_vis_or_private(binding, || self.r.private_vis_import(binding)),
    //     }
    // }

    /// Update effective visibility of a name declaration in the given module,
    /// including its whole reexport chain.
    fn update_binding_effective_visibility(&mut self, parent_mod: LocalDefId, mut decl: Decl<'ra>) {
        let mut parent_id = ParentId::Def(parent_mod);
        while let DeclKind::Import { source_decl, import: _ } = decl.kind {
            self.update_import(decl, parent_id);
            parent_id = ParentId::Import(decl);
            decl = source_decl;
        }

        if let Some(def_id) = decl.res().opt_def_id().and_then(|id| id.as_local()) {
            self.update_def(def_id, decl.vis().expect_local(), parent_id);
        }
    }

    /// All effective visibilities for a node are larger or equal than private visibility
    /// for that node (see `check_invariants` in middle/privacy.rs).
    /// So if either parent or nominal visibility is the same as private visibility, then
    /// `min(parent_vis, nominal_vis) <= private_vis`, and the update logic is guaranteed
    /// to not update anything and we can skip it.
    ///
    /// We are checking this condition only if the correct value of private visibility is
    /// cheaply available, otherwise it doesn't make sense performance-wise.
    ///
    /// `None` is returned if the update can be skipped,
    /// and cheap private visibility is returned otherwise.
    fn may_update(
        &self,
        nominal_vis: Visibility,
        parent_id: ParentId<'_>,
    ) -> Option<Option<Visibility>> {
        match parent_id {
            ParentId::Def(def_id) => (nominal_vis != self.current_private_vis
                && self.r.tcx.local_visibility(def_id) != self.current_private_vis)
                .then_some(Some(self.current_private_vis)),
            ParentId::Import(_) => Some(None),
        }
    }

    fn update_import(&mut self, decl: Decl<'ra>, parent_id: ParentId<'ra>) {
        let nominal_vis = decl.vis().expect_local();
        // let Some(cheap_private_vis) = self.may_update(nominal_vis, parent_id) else { return };
        // let inherited_eff_vis = self.effective_vis_or_private(parent_id);
        // let tcx = self.r.tcx;
        // self.import_effective_visibilities.update(
        //     decl,
        //     Some(nominal_vis),
        //     || cheap_private_vis.unwrap_or_else(|| self.r.private_vis_import(decl)),
        //     inherited_eff_vis,
        //     parent_id.level(),
        //     tcx,
        // );

        let (level, inherited_eff_vis, private_vis) =
            self.parent_level_and_eff_vis_and_private(parent_id);
        let entry = self
            .import_effective_visibilities
            .entry(decl)
            .or_insert(PartialEffectiveVis::from_vis(nominal_vis));
        entry.reexported =
            nominal_vis.min(inherited_eff_vis.reexported, self.r.tcx).max(private_vis, self.r.tcx);
        if level == Level::Direct {
            entry.direct =
                nominal_vis.min(inherited_eff_vis.direct, self.r.tcx).max(private_vis, self.r.tcx);
        }
    }

    fn update_def(
        &mut self,
        def_id: LocalDefId,
        nominal_vis: Visibility,
        parent_id: ParentId<'ra>,
    ) {
        // let Some(cheap_private_vis) = self.may_update(nominal_vis, parent_id) else { return };
        // let inherited_eff_vis = self.effective_vis_or_private(parent_id);
        // let tcx = self.r.tcx;
        // self.def_effective_visibilities.update(
        //     def_id,
        //     Some(nominal_vis),
        //     || cheap_private_vis.unwrap_or_else(|| self.r.private_vis_def(def_id)),
        //     inherited_eff_vis,
        //     parent_id.level(),
        //     tcx,
        // );

        let (level, inherited_eff_vis, private_vis) =
            self.parent_level_and_eff_vis_and_private(parent_id);
        let entry = self
            .def_effective_visibilities
            .entry(def_id)
            .or_insert(PartialEffectiveVis::from_vis(nominal_vis));
        entry.reexported =
            nominal_vis.min(inherited_eff_vis.reexported, self.r.tcx).max(private_vis, self.r.tcx);
        if level == Level::Direct {
            entry.direct =
                nominal_vis.min(inherited_eff_vis.direct, self.r.tcx).max(private_vis, self.r.tcx);
        }
    }

    fn update_field(&mut self, def_id: LocalDefId, parent_id: LocalDefId) {
        let parent_effective_vis = self.def_effective_visibilities.index(&parent_id);
        let nominal_vis = self.r.tcx.local_visibility(def_id);
        let field_vis =
            PartialEffectiveVis::from_vis(nominal_vis).min(*parent_effective_vis, self.r.tcx);
        self.def_effective_visibilities.insert(def_id, field_vis);
    }

    fn parent_level_and_eff_vis_and_private(
        &self,
        id: ParentId<'ra>,
    ) -> (Level, PartialEffectiveVis, Visibility) {
        match id {
            ParentId::Def(def_id) => (
                Level::Direct,
                *self.def_effective_visibilities.index(&def_id),
                self.r.private_vis_def(def_id),
            ),
            ParentId::Import(binding) => (
                Level::Reexported,
                *self.import_effective_visibilities.index(&binding),
                self.r.private_vis_import(binding),
            ),
        }
    }
}

impl<'a, 'ra, 'tcx> Visitor<'a> for EffectiveVisibilitiesVisitor<'a, 'ra, 'tcx> {
    fn visit_item(&mut self, item: &'a ast::Item) {
        let def_id = self.r.local_def_id(item.id);
        // Update effective visibilities of the ADT's fields.
        match item.kind {
            // Resolved in rustc_privacy when types are available
            ast::ItemKind::Impl(..) => return,

            // Should be unreachable at this stage
            ast::ItemKind::MacCall(..) | ast::ItemKind::DelegationMac(..) => panic!(
                "ast::ItemKind::MacCall encountered, this should not anymore appear at this stage"
            ),

            ast::ItemKind::Mod(..) => {
                let prev_private_vis =
                    mem::replace(&mut self.current_private_vis, Visibility::Restricted(def_id));
                visit::walk_item(self, item);
                self.current_private_vis = prev_private_vis;
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
            | ast::ItemKind::Delegation(..) => return,
        }
    }
}
