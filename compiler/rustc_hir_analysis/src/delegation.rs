use itertools::Itertools;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::{ErrorGuaranteed, Span};
use rustc_type_ir::visit::TypeVisitableExt;

type RemapTable = FxHashMap<u32, u32>;

struct IndicesFolder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    remap_table: &'a RemapTable,
}

impl<'tcx, 'a> TypeFolder<TyCtxt<'tcx>> for IndicesFolder<'tcx, 'a> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        if !ty.has_param() {
            return ty;
        }

        if let ty::Param(param) = ty.kind()
            && let Some(idx) = self.remap_table.get(&param.index)
        {
            return Ty::new_param(self.tcx, *idx, param.name);
        }
        ty.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if let ty::ReEarlyParam(param) = r.kind()
            && let Some(idx) = self.remap_table.get(&param.index)
        {
            return ty::Region::new_early_param(
                self.tcx,
                ty::EarlyParamRegion { index: *idx, name: param.name },
            );
        }
        r
    }

    fn fold_const(&mut self, ct: ty::Const<'tcx>) -> ty::Const<'tcx> {
        if let ty::ConstKind::Param(param) = ct.kind()
            && let Some(idx) = self.remap_table.get(&param.index)
        {
            let param = ty::ParamConst::new(*idx, param.name);
            return ty::Const::new_param(self.tcx, param);
        }
        ct.super_fold_with(self)
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum FnKind {
    Free,
    AssocInherentImpl,
    AssocTrait,
    AssocTraitImpl,
}

fn fn_kind<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> FnKind {
    debug_assert!(matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn));

    let parent = tcx.parent(def_id);
    match tcx.def_kind(parent) {
        DefKind::Trait => FnKind::AssocTrait,
        DefKind::Impl { of_trait: true } => FnKind::AssocTraitImpl,
        DefKind::Impl { of_trait: false } => FnKind::AssocInherentImpl,
        _ => FnKind::Free,
    }
}

type OwnParams = Vec<ty::GenericParamDef>;

struct GenericsBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    sig_id: DefId,
    parent: Option<DefId>,
    own_params: OwnParams,
}

impl<'tcx> GenericsBuilder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, sig_id: DefId) -> GenericsBuilder<'tcx> {
        GenericsBuilder { tcx, sig_id, parent: None, own_params: vec![] }
    }

    fn with_parent(mut self, parent: DefId) -> Self {
        self.parent = Some(parent);
        self
    }

    fn with_own_generics(mut self, def_id: DefId) -> Self {
        let generics = self.tcx.generics_of(def_id);
        self.own_params.append(&mut generics.own_params.clone());
        self
    }

    fn with_generics(mut self, def_id: DefId) -> Self {
        let generics = self.tcx.generics_of(def_id);
        if let Some(parent_def_id) = generics.parent {
            self = self.with_own_generics(parent_def_id);
        }
        self.with_own_generics(def_id)
    }

    fn reindex(mut self, offset: u32) -> Self {
        for (idx, param) in self.own_params.iter_mut().enumerate() {
            param.index = idx as u32 + offset;
            // Default type parameters are not inherited: they are not allowed
            // in fn's.
            if let ty::GenericParamDefKind::Type { synthetic, .. } = param.kind {
                param.kind = ty::GenericParamDefKind::Type { has_default: false, synthetic }
            }
        }
        self
    }

    fn process_own_params<F>(mut self, f: F) -> Self
    where
        F: Fn(OwnParams) -> OwnParams,
    {
        self.own_params = f(self.own_params);
        self
    }

    // Lifetime parameters must be declared before type and const parameters.
    // Therefore, When delegating from a free function to a associated function,
    // generic parameters need to be reordered:
    //
    // trait Trait<'a, A> {
    //     fn foo<'b, B>(...) {...}
    // }
    //
    // reuse Trait::foo;
    // desugaring:
    // fn foo<'a, 'b, This: Trait<'a, A>, A, B>(...) {
    //     Trait::foo(...)
    // }
    fn sort(mut self) -> Self {
        self.own_params.sort_by_key(|key| key.kind.is_ty_or_const());
        self
    }

    fn build(self) -> ty::Generics {
        let param_def_id_to_index =
            self.own_params.iter().map(|param| (param.def_id, param.index)).collect();

        let (parent_count, has_self) = self
            .parent
            .and_then(|parent| {
                let parent_generics = self.tcx.generics_of(parent);
                let parent_kind = self.tcx.def_kind(parent);
                Some((parent_generics.count(), parent_kind == DefKind::Trait))
            })
            .unwrap_or((0, false));

        let callee_generics = self.tcx.generics_of(self.sig_id);

        ty::Generics {
            parent: self.parent,
            parent_count,
            own_params: self.own_params,
            param_def_id_to_index,
            has_self,
            has_late_bound_regions: callee_generics.has_late_bound_regions,
            host_effect_index: callee_generics.host_effect_index,
        }
    }
}

struct PredicatesBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    parent: Option<DefId>,
    preds: Vec<(ty::Clause<'tcx>, Span)>,
}

impl<'tcx> PredicatesBuilder<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> PredicatesBuilder<'tcx> {
        PredicatesBuilder { tcx, args, parent: None, preds: vec![] }
    }

    fn with_parent(mut self, parent: DefId) -> Self {
        self.parent = Some(parent);
        self
    }

    fn with_own_preds<F>(mut self, f: F, def_id: DefId) -> Self
    where
        F: Fn(DefId) -> ty::GenericPredicates<'tcx>,
    {
        let preds = f(def_id).instantiate_own(self.tcx, self.args);
        self.preds.extend(preds);
        self
    }

    fn with_preds<F>(mut self, f: F, def_id: DefId) -> Self
    where
        F: Fn(DefId) -> ty::GenericPredicates<'tcx> + Copy,
    {
        let preds = f(def_id);
        if let Some(parent_def_id) = preds.parent {
            self = self.with_own_preds(f, parent_def_id);
        }
        self.with_own_preds(f, def_id)
    }

    fn build(self) -> ty::GenericPredicates<'tcx> {
        ty::GenericPredicates {
            parent: self.parent,
            predicates: self.tcx.arena.alloc_from_iter(self.preds),
            effects_min_tys: ty::List::empty(), // FIXME(fn_delegation): Support effects.
        }
    }
}

fn create_generic_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    sig_id: DefId,
) -> ty::GenericArgsRef<'tcx> {
    let caller_generics = tcx.generics_of(def_id);
    let callee_generics = tcx.generics_of(sig_id);

    let caller_kind = fn_kind(tcx, def_id.into());
    let callee_kind = fn_kind(tcx, sig_id);
    // FIXME(fn_delegation): early bound generics are only supported for trait
    // implementations and free functions. Error was reported in `check_constraints`.
    match (caller_kind, callee_kind) {
        (FnKind::Free, _) => {
            let args = ty::GenericArgs::identity_for_item(tcx, sig_id);
            let mut remap_table: RemapTable = FxHashMap::default();
            for caller_param in &caller_generics.own_params {
                let callee_index =
                    callee_generics.param_def_id_to_index(tcx, caller_param.def_id).unwrap();
                remap_table.insert(callee_index, caller_param.index);
            }
            let mut folder = IndicesFolder { tcx, remap_table: &remap_table };
            args.fold_with(&mut folder)
        }
        (FnKind::AssocTraitImpl, FnKind::AssocTrait) => {
            let parent = tcx.parent(def_id.into());
            let parent_args =
                tcx.impl_trait_header(parent).unwrap().trait_ref.instantiate_identity().args;

            let trait_args = ty::GenericArgs::identity_for_item(tcx, sig_id);
            let method_args = trait_args.iter().skip(callee_generics.parent_count).collect_vec();

            // For trait implementations only the method's own parameters are copied.
            // They need to be reindexed adjusted for impl parameters.
            let mut remap_table: RemapTable = FxHashMap::default();
            let parent_count = caller_generics.parent_count as u32;
            for (idx, callee_own_param) in callee_generics.own_params.iter().enumerate() {
                let callee_index = callee_own_param.index as u32;
                remap_table.insert(callee_index, idx as u32 + parent_count);
            }
            let mut folder = IndicesFolder { tcx, remap_table: &remap_table };
            let method_args = method_args.fold_with(&mut folder);

            tcx.mk_args_from_iter(parent_args.iter().chain(method_args))
        }
        (FnKind::AssocInherentImpl, FnKind::AssocTrait) => {
            let parent = tcx.parent(def_id.into());
            let self_ty = tcx.type_of(parent).instantiate_identity();
            let generic_self_ty = ty::GenericArg::from(self_ty);

            let mut remap_table: RemapTable = FxHashMap::default();
            let trait_args = ty::GenericArgs::identity_for_item(tcx, sig_id);
            let parent_count = caller_generics.parent_count as u32;

            for idx in 1..callee_generics.count() {
                remap_table.insert(idx as u32, idx as u32 + parent_count - 1);
            }

            let mut folder = IndicesFolder { tcx, remap_table: &remap_table };
            let trait_args = trait_args.fold_with(&mut folder);

            let args = std::iter::once(generic_self_ty).chain(trait_args.iter().skip(1));
            let args = tcx.mk_args_from_iter(args);

            args
        }
        // `sig_id` is taken from corresponding trait method
        (FnKind::AssocTraitImpl, _) => unreachable!(),
        _ => ty::GenericArgs::identity_for_item(tcx, sig_id),
    }
}

pub(crate) fn inherit_generics_for_delegation_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    sig_id: DefId,
) -> ty::Generics {
    let caller_kind = fn_kind(tcx, def_id.into());
    let callee_kind = fn_kind(tcx, sig_id);

    let builder = GenericsBuilder::new(tcx, sig_id);

    match (caller_kind, callee_kind) {
        (FnKind::Free, _) => builder.with_generics(sig_id).sort().reindex(0).build(),
        (FnKind::AssocTraitImpl, FnKind::AssocTrait) => {
            let parent = tcx.parent(def_id.into());
            let parent_generics = tcx.generics_of(parent);
            let parent_count = parent_generics.count();

            builder
            .with_parent(parent)
            .with_own_generics(sig_id)
            .reindex(parent_count as u32)
            .build()
        }
        (FnKind::AssocInherentImpl, FnKind::AssocTrait)
        | (FnKind::AssocTrait, FnKind::AssocTrait)
        | (_, FnKind::Free) => {
            let parent = tcx.parent(def_id.into());
            let parent_generics = tcx.generics_of(parent);
            let parent_count = parent_generics.count();

            builder
            .with_parent(parent)
            .with_generics(sig_id)
            .process_own_params(|params| params.iter().skip(1).cloned().collect_vec() )
            .reindex(parent_count as u32)
            .build()
        }
        // `sig_id` is taken from corresponding trait method.
        (FnKind::AssocTraitImpl, _) |
        (_, FnKind::AssocTraitImpl) |
        // delegation to inherent methods is not yet supported
        (_, FnKind::AssocInherentImpl) => unreachable!(),
    }
}

pub(crate) fn inherit_predicates_for_delegation_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    sig_id: DefId,
) -> ty::GenericPredicates<'tcx> {
    let args = create_generic_args(tcx, def_id, sig_id);
    let builder = PredicatesBuilder::new(tcx, args);

    let caller_kind = fn_kind(tcx, def_id.into());
    let callee_kind = fn_kind(tcx, sig_id);
    match (caller_kind, callee_kind) {
        (FnKind::Free, _) => {
            builder.with_preds(|sig_id| tcx.predicates_of(sig_id), sig_id).build()
        }
        (FnKind::AssocTraitImpl, FnKind::AssocTrait) => {
            let parent = tcx.parent(def_id.into());
            builder
            .with_parent(parent)
            .with_own_preds(|sig_id| tcx.predicates_of(sig_id), sig_id)
            .build()
        }
        (FnKind::AssocInherentImpl, FnKind::AssocTrait)
        | (FnKind::AssocTrait, FnKind::AssocTrait)
        | (_, FnKind::Free) => {
            let parent = tcx.parent(def_id.into());
            builder
                .with_parent(parent)
                .with_preds(|sig_id| tcx.explicit_predicates_of(sig_id), sig_id)
                .build()
        }
        // `sig_id` is taken from corresponding trait method.
        (FnKind::AssocTraitImpl, _) |
        (_, FnKind::AssocTraitImpl) |
        // delegation to inherent methods is not yet supported
        (_, FnKind::AssocInherentImpl) => unreachable!(),
    }
}

fn check_constraints<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Result<(), ErrorGuaranteed> {
    let mut ret = Ok(());
    let sig_id = tcx.hir().delegation_sig_id(def_id);
    let span = tcx.def_span(def_id);

    let mut emit = |descr| {
        ret = Err(tcx.dcx().emit_err(crate::errors::UnsupportedDelegation {
            span,
            descr,
            callee_span: tcx.def_span(sig_id),
        }));
    };

    if let Some(local_sig_id) = sig_id.as_local()
        && tcx.hir().opt_delegation_sig_id(local_sig_id).is_some()
    {
        emit("recursive delegation is not supported yet");
    }

    ret
}

pub(crate) fn inherit_sig_for_delegation_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'tcx [Ty<'tcx>] {
    let sig_id = tcx.hir().delegation_sig_id(def_id);
    let caller_sig = tcx.fn_sig(sig_id);
    if let Err(err) = check_constraints(tcx, def_id) {
        let sig_len = caller_sig.instantiate_identity().skip_binder().inputs().len() + 1;
        let err_type = Ty::new_error(tcx, err);
        return tcx.arena.alloc_from_iter((0..sig_len).map(|_| err_type));
    }
    let args = create_generic_args(tcx, def_id, sig_id);

    // Bound vars are also inherited from `sig_id`.
    // They will be rebound later in `lower_fn_ty`.
    let sig = caller_sig.instantiate(tcx, args).skip_binder();
    let sig_it = sig.inputs().iter().cloned().chain(std::iter::once(sig.output()));
    tcx.arena.alloc_from_iter(sig_it)
}
