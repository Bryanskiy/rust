use crate::{FnCtxt, TypeckRootCtxt};

use hir::def::DefKind;
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir as hir;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable};
use rustc_middle::ty::{
    self, GenericArgsRef, GenericParamDef, GenericParamDefKind, Ty, TyCtxt, TypeSuperVisitable,
    TypeVisitable, TypeVisitor,
};
use rustc_span::ErrorGuaranteed;
use rustc_trait_selection::infer::TyCtxtInferExt;

struct DelegationInfo<'tcx> {
    defs: FxIndexMap<DefId, GenericArgsRef<'tcx>>,
    ty_defs: FxIndexMap<ty::TyVid, GenericParamDef>,
    region_defs: FxIndexMap<ty::RegionVid, GenericParamDef>,
}

impl<'tcx> DelegationInfo<'tcx> {
    fn new() -> Self {
        Self {
            defs: FxIndexMap::default(),
            ty_defs: FxIndexMap::default(),
            region_defs: FxIndexMap::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum FnKind {
    Free,
    AssocImpl,
    AssocTrait,
    AssocTraitImpl,
}

fn fn_kind<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> FnKind {
    assert!(matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn));

    let parent = tcx.parent(def_id);
    let parent_kind = tcx.def_kind(parent);
    match parent_kind {
        DefKind::Trait => FnKind::AssocTrait,
        DefKind::Impl { of_trait: true } => FnKind::AssocTraitImpl,
        DefKind::Impl { of_trait: false } => FnKind::AssocImpl,
        _ => FnKind::Free,
    }
}

struct GenericsReindexer<'tcx> {
    tcx: TyCtxt<'tcx>,
    ty_idx: FxIndexMap<u32, u32>,
    re_idx: FxIndexMap<u32, u32>,
    offset: u32,
}

impl<'tcx> GenericsReindexer<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, offset: u32) -> Self {
        Self { tcx, ty_idx: FxIndexMap::default(), re_idx: FxIndexMap::default(), offset }
    }
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for GenericsReindexer<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        if let ty::Param(param) = ty.kind() {
            let len = self.ty_idx.len() as u32 + self.offset;
            let idx = *self.ty_idx.entry(param.index).or_insert(len);
            let new_param = Ty::new_param(self.tcx, idx, param.name);
            return new_param;
        }
        ty.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        if let ty::RegionKind::ReEarlyParam(re) = r.kind() {
            let len = self.re_idx.len() as u32 + self.offset;
            let index = *self.re_idx.entry(re.index).or_insert(len);
            let new_region = ty::Region::new_early_param(
                self.tcx,
                ty::EarlyParamRegion { def_id: re.def_id, index, name: re.name },
            );
            return new_region;
        }

        r
    }
}

struct DelegationInfoCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    info: DelegationInfo<'tcx>,
    def_id: LocalDefId,
}

impl<'tcx> DelegationInfoCollector<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> Self {
        Self { tcx, info: DelegationInfo::new(), def_id }
    }

    fn collect(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> DelegationInfo<'tcx> {
        let mut collector = Self::new(tcx, def_id);

        let sig_id = tcx.hir().delegation_sig_id(def_id);
        let caller_kind = fn_kind(tcx, def_id.into());
        let callee_kind = fn_kind(tcx, sig_id);

        match (caller_kind, callee_kind) {
            (FnKind::Free, _) => {
                let path = collector.check_call();
                path.visit_with(&mut collector);
            }

            (FnKind::AssocTraitImpl, FnKind::AssocTrait)
            | (FnKind::AssocImpl, FnKind::AssocTrait) => {
                let parent = tcx.parent(def_id.into());
                let sig_generics = tcx.generics_of(sig_id);
                let parent_generics = tcx.generics_of(parent);

                let parent_args = tcx.impl_trait_header(parent).unwrap().trait_ref.instantiate_identity().args;
                println!("parent_args {:?}", parent_args);
                let trait_args = ty::GenericArgs::identity_for_item(tcx, sig_id);
                println!("trait_args {:?}", trait_args);
                let method_args = trait_args.iter().skip(sig_generics.parent_count).collect_vec();
                println!("method_args before {:?}", method_args);
                let mut reindexer = GenericsReindexer::new(tcx, (parent_generics.own_params.len()) as u32);
                let method_args = method_args.fold_with(&mut reindexer);
                println!("method_args after {:?}", method_args);

                let args = tcx.mk_args_from_iter(parent_args.iter().chain(method_args));
                println!("args {:?}", args);

                collector.info.defs.insert(def_id.into(), args);
            }

            _ => {}
        }

        collector.info
    }

    // Collect generic parameters definitions during callee type traversal according to
    // encountered inference variables.
    fn extract_info_from_def(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>) {
        let generics = self.tcx.generics_of(def_id);

        for (idx, arg) in args.iter().enumerate() {
            if let Some(ty) = arg.as_type()
                && let ty::Infer(ty::InferTy::TyVar(ty_vid)) = ty.kind()
            {
                self.info.ty_defs.insert(*ty_vid, generics.param_at(idx, self.tcx).clone());
            } else if let Some(re) = arg.as_region()
                && let ty::RegionKind::ReVar(inf_re) = re.kind()
            {
                self.info.region_defs.insert(inf_re, generics.param_at(idx, self.tcx).clone());
            }
        }

        self.info.defs.insert(def_id, args);
    }

    // Extract callee type from the call path. Should only be used for
    // non-associated delegation items. For example in
    //
    // trait Trait<T> {
    //     fn foo<U>(&self, x: U, y: T);
    // }
    //
    // reuse <u16 as Trait<_>>::foo;
    //
    // it will return `FnDef(DefId(Trait::foo), [u16, ?0t, ?1t])`.
    fn check_call(&self) -> Ty<'tcx> {
        let body = self.tcx.hir().body_owned_by(self.def_id);
        let body = self.tcx.hir().body(body);

        let (expr, callee, args) = match body.value.kind {
            hir::ExprKind::Block(
                hir::Block {
                    expr: expr @ Some(hir::Expr { kind: hir::ExprKind::Call(callee, args), .. }),
                    ..
                },
                _,
            ) => (expr.unwrap(), callee, args),
            _ => unreachable!(),
        };

        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        // FIXME: cycle error on `with_opaque_type_inference`
        let root_ctxt =
            TypeckRootCtxt::new_with_infcx(self.tcx, self.def_id, infcx);
        let param_env = ty::ParamEnv::empty();
        let fcx = FnCtxt::new(&root_ctxt, param_env, self.def_id);
        fcx.check_expr_with_expectation_and_args(
            callee,
            crate::expectation::Expectation::NoExpectation,
            args,
            Some(expr),
        )
    }
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for DelegationInfoCollector<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        match ty.kind() {
            ty::Adt(adt, args) => self.extract_info_from_def(adt.did(), args),
            ty::FnDef(did, args) => self.extract_info_from_def(*did, args),
            _ => {}
        }

        ty.super_visit_with(self)
    }
}

struct DelegationArgFolder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    info: &'a DelegationInfo<'tcx>,
}

impl<'tcx, 'a> DelegationArgFolder<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, info: &'a DelegationInfo<'tcx>) -> Self {
        Self { tcx, info }
    }
}

impl<'tcx, 'a> TypeFolder<TyCtxt<'tcx>> for DelegationArgFolder<'tcx, 'a> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        if let ty::Infer(inf_ty) = ty.kind()
            && let ty::InferTy::TyVar(vid) = inf_ty
        {
            let param = self.info.ty_defs[vid].clone();
            let index = vid.as_u32() + self.info.region_defs.len() as u32;
            return Ty::new_param(self.tcx, index, param.name);
        };
        ty.super_fold_with(self)
    }

    fn fold_region(&mut self, r: ty::Region<'tcx>) -> ty::Region<'tcx> {
        let ty::RegionKind::ReVar(rid) = &r.kind() else {
            return r;
        };
        let param = &self.info.region_defs[rid];
        ty::Region::new_early_param(
            self.tcx,
            ty::EarlyParamRegion { def_id: param.def_id, index: rid.as_u32(), name: param.name },
        )
    }
}

struct DelegationResolver<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    info: &'a DelegationInfo<'tcx>,
    def_id: LocalDefId,
    sig_id: DefId,
}

impl<'tcx, 'a> DelegationResolver<'tcx, 'a> {
    fn new(tcx: TyCtxt<'tcx>, def_id: LocalDefId, info: &'a DelegationInfo<'tcx>) -> Self {
        Self { tcx, info, def_id, sig_id: tcx.hir().delegation_sig_id(def_id) }
    }

    fn fn_sig(&self) -> (&'tcx [Ty<'tcx>], Ty<'tcx>) {
        let caller_sig = self.tcx.fn_sig(self.sig_id);

        let caller_kind = fn_kind(self.tcx, self.def_id.into());
        let callee_kind = fn_kind(self.tcx, self.sig_id);

        let sig = match (caller_kind, callee_kind) {
            (FnKind::Free, _) => {
                let mut args = self.info.defs[&self.sig_id];
                let mut folder = DelegationArgFolder::new(self.tcx, self.info);
                args = args.fold_with(&mut folder);

                caller_sig.instantiate(self.tcx, args)
            }
            // only `Self` param supported here
            (FnKind::AssocTraitImpl, FnKind::AssocTrait)
            | (FnKind::AssocImpl, FnKind::AssocTrait) => {
                let args = self.info.defs[&self.def_id.to_def_id()];
                println!("instantiate args: {:?}", args);
                caller_sig.instantiate(self.tcx, args)

            }
            // here generics are not yet supported
            _ => caller_sig.instantiate_identity(),
        };
        // Bound vars are also inherited from `sig_id`.
        // They will be rebound later in `lower_fn_ty`.
        let sig = sig.skip_binder();
        (sig.inputs(), sig.output())
    }

    fn generics_of(&self) -> Option<ty::Generics> {
        let callee_generics = self.tcx.generics_of(self.sig_id);

        let caller_kind = fn_kind(self.tcx, self.def_id.into());
        let callee_kind = fn_kind(self.tcx, self.sig_id);

        match (caller_kind, callee_kind) {
            (FnKind::Free, _) => {
                let mut ty_params =
                    self.info.ty_defs.iter().map(|(_, param)| param.clone()).collect_vec();
                let mut region_params =
                    self.info.region_defs.iter().map(|(_, param)| param.clone()).collect_vec();

                region_params.append(&mut ty_params);
                let mut own_params = region_params;

                // Default type parameters are not supported: they must be trailing,
                // but we collect parameters by depth-first callee type traversal.
                for (idx, param) in own_params.iter_mut().enumerate() {
                    param.index = idx as u32;
                    if let GenericParamDefKind::Type { synthetic, .. } = param.kind {
                        param.kind = GenericParamDefKind::Type { has_default: false, synthetic }
                    }
                }

                let param_def_id_to_index =
                    own_params.iter().map(|param| (param.def_id, param.index)).collect();

                Some(ty::Generics {
                    parent: None,
                    parent_count: 0,
                    own_params,
                    param_def_id_to_index,
                    has_self: false,
                    has_late_bound_regions: callee_generics.has_late_bound_regions,
                    host_effect_index: None,
                })
            }

            (FnKind::AssocTraitImpl, FnKind::AssocTrait)
            | (FnKind::AssocImpl, FnKind::AssocTrait) => {
                let parent = self.tcx.parent(self.def_id.into());
                let parent_generics = self.tcx.generics_of(parent);
                let parent_count = parent_generics.parent_count + parent_generics.own_params.len();

                let mut own_params = self.tcx.generics_of(self.sig_id).own_params.clone();
                for (idx, param) in own_params.iter_mut().enumerate() {
                    param.index = (parent_count + idx) as u32;
                }

                let param_def_id_to_index =
                    own_params.iter().map(|param| (param.def_id, param.index)).collect();

                Some(ty::Generics {
                    parent: Some(parent),
                    parent_count,
                    own_params,
                    param_def_id_to_index,
                    has_self: false,
                    has_late_bound_regions: callee_generics.has_late_bound_regions,
                    host_effect_index: None,
                })
            }
            // here generics are not yet supported
            _ => None,
        }
    }

    fn predicates_of(&self) -> Option<ty::GenericPredicates<'tcx>> {
        let caller_kind = fn_kind(self.tcx, self.def_id.into());
        let callee_kind = fn_kind(self.tcx, self.sig_id);

        match (caller_kind, callee_kind) {
            (FnKind::Free, _) => {
                let mut predicates = vec![];
                for (def_id, args) in self.info.defs.iter() {
                    let def_predicates = self.tcx.explicit_predicates_of(def_id);
                    let mut instantiated_predicates =
                        def_predicates.instantiate(self.tcx, args).into_iter().collect_vec();
                    predicates.append(&mut instantiated_predicates);
                }

                let span = self.tcx.def_span(self.def_id);
                for predicate in predicates.iter_mut() {
                    predicate.1 = span;
                }

                let mut folder = DelegationArgFolder::new(self.tcx, self.info);
                let predicates = predicates.fold_with(&mut folder);
                let predicates = self.tcx.arena.alloc_from_iter(predicates);
                Some(ty::GenericPredicates { parent: None, predicates })
            }
            (FnKind::AssocTraitImpl, FnKind::AssocTrait)
            | (FnKind::AssocImpl, FnKind::AssocTrait) => {
                let parent = self.tcx.parent(self.def_id.into());
                let predicates = self.tcx.explicit_predicates_of(self.sig_id);
                let args = self.info.defs[&self.def_id.to_def_id()];

                let instantiated_predicates =
                    predicates.instantiate(self.tcx, args).into_iter().collect_vec();

                let predicates = self.tcx.arena.alloc_from_iter(instantiated_predicates);
                Some(ty::GenericPredicates { parent:  Some(parent), predicates })

            }
            // here generics are not yet supported
            _ => None,
        }
    }

    fn check_constraints(&self) -> Result<(), ErrorGuaranteed> {
        let mut ret = Ok(());

        let tcx = self.tcx;
        let span = tcx.def_span(self.def_id);
        let sig_id = self.sig_id;

        let sig_span = tcx.def_span(sig_id);
        let mut emit = |descr| {
            ret = Err(tcx.dcx().emit_err(crate::errors::NotSupportedDelegation {
                span,
                descr,
                callee_span: sig_span,
            }));
        };

        if let Some(node) = tcx.hir().get_if_local(sig_id)
            && let Some(decl) = node.fn_decl()
            && let hir::FnRetTy::Return(ty) = decl.output
            && let hir::TyKind::InferDelegation(_, _) = ty.kind
        {
            emit("recursive delegation is not supported yet");
        }

        ret
    }
}

fn generate_error_results<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    err: ErrorGuaranteed,
) -> ty::DelegationResults<'tcx> {
    let sig_id = tcx.hir().delegation_sig_id(def_id);
    let sig_len = tcx.fn_arg_names(sig_id).len();
    let err_type = Ty::new_error(tcx, err);
    let inputs = tcx.arena.alloc_from_iter((0..sig_len).map(|_| err_type));
    ty::DelegationResults { inputs, output: err_type, generics: None, predicates: None }
}

pub fn resolve_delegation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> ty::DelegationResults<'tcx> {
    let info = DelegationInfoCollector::collect(tcx, def_id);
    let delegation_resolver = DelegationResolver::new(tcx, def_id, &info);
    if let Err(err) = delegation_resolver.check_constraints() {
        return generate_error_results(tcx, def_id, err);
    }
    let (inputs, output) = delegation_resolver.fn_sig();
    println!("input: {:?}", inputs);
    println!("output: {:?}", output);
    let generics = delegation_resolver.generics_of();
    println!("generics: {:?}", generics);
    let predicates = delegation_resolver.predicates_of();
    println!("predicates: {:?}", predicates);

    ty::DelegationResults { inputs, output, generics, predicates }
}
