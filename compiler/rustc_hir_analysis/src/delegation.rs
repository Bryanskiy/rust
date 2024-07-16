use itertools::Itertools;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::ErrorGuaranteed;
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

            let callee_generics = tcx.generics_of(sig_id);
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
        // only `Self` param supported here
        (FnKind::AssocInherentImpl, FnKind::AssocTrait) => {
            let parent = tcx.parent(def_id.into());
            let self_ty = tcx.type_of(parent).instantiate_identity();
            let generic_self_ty = ty::GenericArg::from(self_ty);
            tcx.mk_args_from_iter(std::iter::once(generic_self_ty))
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
) -> Option<ty::Generics> {
    let caller_kind = fn_kind(tcx, def_id.into());
    let callee_kind = fn_kind(tcx, sig_id);

    let param_def_id_to_index = |own_params: &Vec<ty::GenericParamDef>| {
        own_params.iter().map(|param| (param.def_id, param.index)).collect()
    };

    // FIXME(fn_delegation): early bound generics are only supported for trait
    // implementations and free functions. Error was reported in `check_constraints`.
    match (caller_kind, callee_kind) {
        (FnKind::Free, _) => {
            let mut own_params = vec![];

            let callee_generics = tcx.generics_of(sig_id);
            if let Some(parent_sig_id) = callee_generics.parent {
                let parent_sig_generics = tcx.generics_of(parent_sig_id);
                own_params.append(&mut parent_sig_generics.own_params.clone());
            }
            own_params.append(&mut callee_generics.own_params.clone());

            // lifetimes go first
            own_params.sort_by_key(|key| key.kind.is_ty_or_const());

            for (idx, param) in own_params.iter_mut().enumerate() {
                param.index = idx as u32;
                // Default type parameters are not inherited: they are not allowed
                // in fn's.
                if let ty::GenericParamDefKind::Type { synthetic, .. } = param.kind {
                    param.kind = ty::GenericParamDefKind::Type { has_default: false, synthetic }
                }
            }

            Some(ty::Generics {
                parent: None,
                parent_count: 0,
                param_def_id_to_index: param_def_id_to_index(&own_params),
                own_params,
                has_self: false,
                has_late_bound_regions: callee_generics.has_late_bound_regions,
                host_effect_index: None,
            })
        }
        (FnKind::AssocTraitImpl, FnKind::AssocTrait) => {
            let callee_generics = tcx.generics_of(sig_id);

            let parent = tcx.parent(def_id.into());
            let parent_generics = tcx.generics_of(parent);
            let parent_count = parent_generics.count();

            let mut own_params = tcx.generics_of(sig_id).own_params.clone();
            for (idx, param) in own_params.iter_mut().enumerate() {
                param.index = (parent_count + idx) as u32;
            }

            Some(ty::Generics {
                parent: Some(parent),
                parent_count,
                param_def_id_to_index: param_def_id_to_index(&own_params),
                own_params,
                has_self: false,
                has_late_bound_regions: callee_generics.has_late_bound_regions,
                host_effect_index: None,
            })
        }
        // `sig_id` is taken from corresponding trait method
        (FnKind::AssocTraitImpl, _) => unreachable!(),
        _ => None,
    }
}

pub(crate) fn inherit_predicates_for_delegation_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    sig_id: DefId,
) -> Option<ty::GenericPredicates<'tcx>> {
    // FIXME(fn_delegation): early bound generics are only supported for trait
    // implementations and free functions. Error was reported in `check_constraints`.
    let caller_kind = fn_kind(tcx, def_id.into());
    if caller_kind != FnKind::Free && caller_kind != FnKind::AssocTraitImpl {
        return None;
    }

    let callee_predicates = tcx.predicates_of(sig_id);
    let args = create_generic_args(tcx, def_id, sig_id);

    let mut preds = vec![];
    if let Some(parent_id) = callee_predicates.parent {
        preds.extend(tcx.predicates_of(parent_id).instantiate_own(tcx, args));
    }
    preds.extend(callee_predicates.instantiate_own(tcx, args));

    let parent = match fn_kind(tcx, def_id.to_def_id()) {
        FnKind::Free => None,
        _ => Some(tcx.parent(def_id.into())),
    };

    Some(ty::GenericPredicates {
        parent,
        predicates: tcx.arena.alloc_from_iter(preds),
        effects_min_tys: ty::List::empty(),
    })
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

    let caller_kind = fn_kind(tcx, def_id.into());
    let callee_kind = fn_kind(tcx, sig_id);

    match (caller_kind, callee_kind) {
        (FnKind::Free, _) | (FnKind::AssocTraitImpl, FnKind::AssocTrait) => {}
        // `sig_id` is taken from corresponding trait method
        (FnKind::AssocTraitImpl, _) => {
            return Err(tcx
                .dcx()
                .span_delayed_bug(span, "unexpected callee path resolution in delegation item"));
        }
        _ => {
            let sig_generics = tcx.generics_of(sig_id);
            let parent = tcx.parent(def_id.into());
            let parent_generics = tcx.generics_of(parent);

            let sig_has_self = sig_generics.has_self as usize;
            let parent_has_self = parent_generics.has_self as usize;

            if sig_generics.count() > sig_has_self || parent_generics.count() > parent_has_self {
                emit(
                    "early bound generics are only supported for trait implementations and free functions",
                );
            }
        }
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
