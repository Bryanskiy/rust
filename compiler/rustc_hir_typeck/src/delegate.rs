use hir::intravisit::{self, Visitor};
use hir::{Delegation, ExprKind};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir as hir;
use rustc_middle::hir::{nested_filter, DelegationResults};
use rustc_middle::query::Providers;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_type_ir::fold::TypeSuperFoldable;
use ty::fold::{TypeFoldable, TypeFolder};

pub struct TyPrinter<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for TyPrinter<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        println!("TyPrinter: {:?}", ty.kind());
        ty.super_fold_with(self)
    }
}

struct SelfReplaceFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    target: Ty<'tcx>,
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for SelfReplaceFolder<'tcx> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // FIXME: better to compare Self types, see `compare_method_predicate_entailment`
    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match *ty.kind() {
            ty::Ref(..) | ty::Bound(..) => ty.super_fold_with(self),
            _ => self.target,
        }
    }
}

struct GenericsReplaceFolder<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    replace_map: &'a ReplaceMap<'tcx>,
}

impl<'tcx, 'a> GenericsReplaceFolder<'tcx, 'a> {
    fn bitwise_comparison(lhs: Ty<'tcx>, rhs: Ty<'tcx>) -> bool {
        match (lhs.kind(), rhs.kind()) {
            (ty::Param(l), ty::Param(r)) => l == r,
            (ty::Bound(li, l), ty::Bound(ri, r)) => li == ri && l == r,
            _ => false,
        }
    }
}

impl<'tcx, 'a> TypeFolder<TyCtxt<'tcx>> for GenericsReplaceFolder<'tcx, 'a> {
    fn interner(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    // FIXME same for regions
    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        for (before, after) in self.replace_map.iter() {
            if let Some(before_ty) = before.as_type() && Self::bitwise_comparison(before_ty, ty) {
                return after.expect_ty();
            }
        }
        ty.super_fold_with(self)
    }
}

struct ProxyResolver<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    // method resolution
    result: Option<DefId>,
}

impl<'tcx> ProxyResolver<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, typeck: &'tcx TypeckResults<'tcx>) -> Self {
        Self { tcx, typeck, result: None }
    }

    fn resolve(tcx: TyCtxt<'tcx>, def_id: DefId) -> DefId {
        let proxy = Self::get_proxy_impl_item(tcx, def_id);

        // FIXME: delegation to !fn not supported error
        let hir::ImplItemKind::Fn(_, body_id) = proxy.kind else {
            bug!("delegation: expected ImplItemKind::Fn");
        };

        let typeck = tcx.typeck_body(body_id);
        let mut visitor = Self::new(tcx, typeck);
        intravisit::walk_impl_item(&mut visitor, proxy);

        visitor.result.expect("couldn't resolve delegation fn")
    }

    fn get_proxy_impl_item(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx hir::ImplItem<'tcx> {
        let parent = tcx.parent(def_id);
        if let Delegation::Gen { explicit_self: _, proxy } = tcx.delegation_kind(def_id) {
            let impl_ = tcx.hir().expect_item(parent.expect_local()).expect_impl();
            for impl_item_ref in impl_.items {
                if impl_item_ref.ident.name == proxy {
                    return tcx.hir().impl_item(impl_item_ref.id);
                }
            }
        }

        bug!("Associative proxy fn not found for {def_id:?} def_id")
    }
}

impl<'tcx> Visitor<'tcx> for ProxyResolver<'tcx> {
    type NestedFilter = nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if self.result.is_some() {
            return;
        }

        if let ExprKind::MethodCall(_, _, args, _) = expr.kind &&
            args.len() == 1 &&
            let ExprKind::Underscore = args[0].kind
        {
            self.result = self.typeck.type_dependent_def_id(expr.hir_id);
            return;
        }

        intravisit::walk_expr(self, expr)
    }
}

fn impl_item_self_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Ty<'tcx> {
    let parent = tcx.parent(def_id);
    tcx.type_of(parent).skip_binder()
}

type ReplaceMap<'tcx> = FxHashMap<ty::GenericArg<'tcx>, ty::GenericArg<'tcx>>;

struct GenericsInferenceResult<'tcx> {
    generics: ty::Generics,
    replace_map: ReplaceMap<'tcx>,
}

struct DelegationCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
}

impl<'tcx> DelegationCtx<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self { tcx, def_id }
    }

    fn infer_sig<'a>(&self, res: DefId, replace_map: &'a ReplaceMap<'tcx>) -> ty::PolyFnSig<'tcx> {
        let res_sig = self.tcx.fn_sig(res);
        let res_bound_vars = res_sig.skip_binder().bound_vars();

        let assoc_item = self.tcx.associated_item(res);
        let new_sig = if assoc_item.container == ty::AssocItemContainer::TraitContainer {
            // FIXME: check assoc_item.fn_has_self_parameter

            let self_ty = ty::GenericArg::from(impl_item_self_ty(self.tcx, self.def_id));
            let res_substs = ty::InternalSubsts::identity_for_item(self.tcx, res);

            let substs_iter = std::iter::once(self_ty).chain(res_substs.iter().skip(1));
            let substs = self.tcx.mk_substs_from_iter(substs_iter);
            let sig = res_sig.subst(self.tcx, substs).skip_binder();

            let mut folder = GenericsReplaceFolder { tcx: self.tcx, replace_map };
            let new_inputs: Vec<_> = sig
                .inputs()
                .iter()
                .enumerate()
                .map(|(idx, input)| if idx != 0 { input.fold_with(&mut folder) } else { *input })
                .collect();
            let new_output = sig.output().fold_with(&mut folder);

            let new_sig =
                self.tcx.mk_fn_sig(new_inputs, new_output, sig.c_variadic, sig.unsafety, sig.abi);

            ty::Binder::bind_with_vars(new_sig, res_bound_vars)
        } else {
            let mut folder = SelfReplaceFolder {
                tcx: self.tcx,
                target: impl_item_self_ty(self.tcx, self.def_id),
            };

            let sig = res_sig.skip_binder().skip_binder();

            let new_inputs: Vec<_> = sig
                .inputs()
                .iter()
                .enumerate()
                .map(
                    |(idx, param_ty)| {
                        if idx == 0 { param_ty.fold_with(&mut folder) } else { *param_ty }
                    },
                )
                .collect();

            let new_sig =
                self.tcx.mk_fn_sig(new_inputs, sig.output(), sig.c_variadic, sig.unsafety, sig.abi);
            ty::Binder::bind_with_vars(new_sig, res_bound_vars)
        };

        new_sig
    }

    fn infer_predicates<'a>(
        &self,
        res: DefId,
        replace_map: &'a ReplaceMap<'tcx>,
    ) -> ty::GenericPredicates<'tcx> {
        let mut res_predicates = self.tcx.predicates_of(res);
        res_predicates.parent = Some(self.tcx.parent(self.def_id));
        let mut folder = GenericsReplaceFolder { tcx: self.tcx, replace_map };

        let new_predicates = self.tcx.arena.alloc_from_iter(
            res_predicates.predicates.iter().map(|clause| clause.fold_with(&mut folder)),
        );

        res_predicates.predicates = new_predicates;
        res_predicates
    }

    fn infer_generics(&self, res: DefId) -> GenericsInferenceResult<'tcx> {
        let res_generics = self.tcx.generics_of(res);
        let mut infered_generics = res_generics.clone();
        let parent_generics = self.tcx.generics_of(self.tcx.parent(self.def_id));

        infered_generics.parent = Some(self.tcx.parent(self.def_id));
        infered_generics.parent_count = parent_generics.parent_count + parent_generics.params.len();
        infered_generics.has_self = false;
        infered_generics.params = infered_generics.params;

        let mut replace_map: ReplaceMap<'tcx> = FxHashMap::default();
        let offset = infered_generics.parent_count as i32 - res_generics.parent_count as i32;

        for def in &mut infered_generics.params {
            let ty_before = self.tcx.mk_param_from_def(&def);
            // FIXME: generics renaming in case of ambiguity
            def.index = if offset.is_negative() {
                def.index - offset.wrapping_abs() as u32
            } else {
                def.index + offset as u32
            };
            let ty_after = self.tcx.mk_param_from_def(&def);
            assert!(matches!(replace_map.insert(ty_before, ty_after), None));
        }

        GenericsInferenceResult { generics: infered_generics, replace_map }
    }

    fn delegate(&self) -> &'tcx DelegationResults<'tcx> {
        let res = ProxyResolver::resolve(self.tcx, self.def_id);

        let generics = self.infer_generics(res);
        self.tcx.arena.alloc(DelegationResults {
            sig: self.infer_sig(res, &generics.replace_map),
            predicates: self.infer_predicates(res, &generics.replace_map),
            generics: generics.generics,
        })
    }
}

pub fn delegation_kind<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> hir::Delegation {
    if let Some(node) = tcx.hir().get_if_local(def_id) &&
    let rustc_hir::Node::ImplItem(impl_item) = node {
        return impl_item.delegation;
    }

    hir::Delegation::None
}

pub fn delegate<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> &'tcx DelegationResults<'tcx> {
    let ctx = DelegationCtx::new(tcx, def_id);
    ctx.delegate()
}

pub fn provide(providers: &mut Providers) {
    *providers = Providers { delegate, delegation_kind, ..*providers };
}
