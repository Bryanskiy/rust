use hir::intravisit::{self, Visitor};
use hir::{Delegation, ExprKind};
use rustc_hir as hir;
use rustc_middle::hir::{nested_filter, DelegationResults};
use rustc_middle::query::Providers;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::def_id::DefId;
use rustc_type_ir::fold::TypeSuperFoldable;
use ty::fold::{TypeFoldable, TypeFolder};

struct ReplaceFolder<'tcx> {
    tcx: TyCtxt<'tcx>,
    target: Ty<'tcx>,
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for ReplaceFolder<'tcx> {
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

        // FIXME: report error if method call wasn't found
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

struct DelegationCtx<'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
}

impl<'tcx> DelegationCtx<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self { tcx, def_id }
    }

    fn infer_sig(&self, res: DefId) -> ty::PolyFnSig<'tcx> {
        let res_sig = self.tcx.fn_sig(res);
        let res_bound_vars = res_sig.skip_binder().bound_vars();

        let (inputs, output, c_variadic, unsafety, abi) = if self.tcx.associated_item(res).container
            == ty::AssocItemContainer::TraitContainer
        {
            let self_ty = ty::GenericArg::from(impl_item_self_ty(self.tcx, self.def_id));

            let own_substs = self
                .tcx
                .generics_of(res)
                .own_substs(ty::InternalSubsts::identity_for_item(self.tcx, res));

            let substs_iter = std::iter::once(self_ty).chain(own_substs.iter().copied());
            let substs = self.tcx.mk_substs_from_iter(substs_iter);
            let sig = res_sig.subst(self.tcx, substs.as_slice()).skip_binder();
            let new_inputs: Vec<_> = sig.inputs().iter().copied().collect();
            (new_inputs, sig.output(), sig.c_variadic, sig.unsafety, sig.abi)
        } else {
            let mut folder =
                ReplaceFolder { tcx: self.tcx, target: impl_item_self_ty(self.tcx, self.def_id) };

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

            (new_inputs, sig.output(), sig.c_variadic, sig.unsafety, sig.abi)
        };

        let new_sig = self.tcx.mk_fn_sig(inputs, output, c_variadic, unsafety, abi);
        println!("new sig: {:?}", new_sig);

        ty::Binder::bind_with_vars(new_sig, res_bound_vars)
    }

    fn infer_predicates(&self, res: DefId) -> ty::GenericPredicates<'tcx> {
        let mut res_predicates = self.tcx.predicates_of(res);
        res_predicates.parent = Some(self.tcx.parent(self.def_id));
        println!("new predicates: {:?}", res_predicates);
        res_predicates
    }

    // FIXME: if parent contains generics -> TypeFolder for reordering params
    fn infer_generics(&self, res: DefId) -> ty::Generics {
        let mut res_generics = self.tcx.generics_of(res).clone();
        res_generics.parent = Some(self.tcx.parent(self.def_id));
        println!("new generics: {:?}", res_generics);
        res_generics
    }

    fn delegate(&self) -> &'tcx DelegationResults<'tcx> {
        let res = ProxyResolver::resolve(self.tcx, self.def_id);

        self.tcx.arena.alloc(DelegationResults {
            sig: self.infer_sig(res),
            predicates: self.infer_predicates(res),
            generics: self.infer_generics(res),
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
