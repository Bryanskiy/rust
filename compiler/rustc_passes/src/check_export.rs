use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{self as hir, self, HirId};
use rustc_middle::hir::nested_filter;
use rustc_middle::middle::privacy::{EffectiveVisibility, Level};
use rustc_middle::ty::{
    self, Ty, TyCtxt, TypeSuperVisitable, TypeVisitable, TypeVisitor, Visibility,
};
use rustc_span::{Span, sym};
use rustc_target::spec::abi::Abi;

// use rustc_trait_selection::infer::TyCtxtInferExt;
// use rustc_trait_selection::traits::{self, ObligationCtxt};
use crate::errors;

struct TypeIsExportableChecker<'tcx> {
    is_ret: bool,
    tcx: TyCtxt<'tcx>,
    span: Span,
}

impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for TypeIsExportableChecker<'tcx> {
    fn visit_ty(&mut self, ty: Ty<'tcx>) {
        match ty.kind() {
            ty::Adt(adt_def, _) => {
                let def_id = adt_def.did();
                if self.tcx.get_attr(def_id, sym::export).is_none() {
                    self.tcx.dcx().emit_err(errors::UnexportableItem {
                        descr: "fn with not exportable nested type",
                        span: self.span,
                    });
                    return;
                }
            }
            // Primitive types are exportable
            ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Bool | ty::Char => {}

            // TODO: references are ABI safe?
            ty::Ref(..) => {
                return;
            }

            // FIXME: rewrite like in `types.rs` for FFI safaty
            ty::Tuple(tys) if self.is_ret && tys.is_empty() => {}

            ty::Array(..)
            | ty::Closure(..)
            | ty::Param(_)
            | ty::Dynamic(..)
            | ty::Coroutine(..)
            | ty::Foreign(_)
            | ty::Str
            | ty::Tuple(_)
            | ty::Pat(..)
            | ty::Slice(_)
            | ty::RawPtr(..)
            | ty::FnDef(..)
            | ty::FnPtr(..)
            | ty::CoroutineClosure(..)
            | ty::CoroutineWitness(..)
            | ty::Never => {
                self.tcx.dcx().emit_err(errors::UnexportableItem {
                    descr: &format!("{}", ty),
                    span: self.span,
                });
            }

            ty::Alias(..) | ty::Infer(_) | ty::Placeholder(_) | ty::Bound(..) => unreachable!(),

            ty::Error(_) => {}
        }
        ty.super_visit_with(self)
    }
}

// TODO: exportable set for mangling. See `OpaqueTypeCollector` for example.
struct CheckExportVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

// Which types are exportable but not FFI-safe?
// TODO: returns after errors emit.
impl<'tcx> CheckExportVisitor<'tcx> {
    /// Only non-generic functions with a stable ABI (e.g. extern "C") are exportable.
    /// TODO: nested types have `#[export]`
    fn check_fn(&self, def_id: DefId) {
        let span = self.tcx.def_span(def_id);
        self.check_generics(def_id);

        // TODO: skip binder safety?
        let sig = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
        if !matches!(sig.abi, Abi::C { .. }) {
            self.tcx
                .dcx()
                .emit_err(errors::UnexportableItem { descr: "non \"C\" ABI function", span });
        }

        let param_env = ty::ParamEnv::reveal_all();
        let sig = self.tcx.try_normalize_erasing_regions(param_env, sig).unwrap_or(sig);

        for input in sig.inputs().iter() {
            let mut visitor = TypeIsExportableChecker { tcx: self.tcx, span, is_ret: false };
            input.visit_with(&mut visitor);
        }
        let mut visitor = TypeIsExportableChecker { tcx: self.tcx, span, is_ret: true };
        sig.output().visit_with(&mut visitor);
    }

    /// Only structs/enums/unions with a stable representation (e.g. repr(i32) or repr(C)).
    /// are exportable.
    fn check_ty(&self, def_id: DefId, _span: Span) {
        // TODO: skip binder safety?
        let ty = self.tcx.type_of(def_id).skip_binder();

        if let ty::Adt(adt_def, _) = ty.kind() {
            // FIXME: anything else?
            if !adt_def.repr().c() {
                self.tcx.dcx().emit_err(errors::UnexportableItem {
                    descr: "type without stable representation",
                    span: self.tcx.def_span(def_id),
                });
            }
        }
    }

    fn check_alias(&self, def_id: DefId, span: Span) {
        // TODO: skip binder safety?
        let ty = self.tcx.type_of(def_id).skip_binder();
        let param_env = ty::ParamEnv::reveal_all();
        let ty = self.tcx.try_normalize_erasing_regions(param_env, ty).unwrap_or(ty);
        let mut visitor = TypeIsExportableChecker { tcx: self.tcx, span, is_ret: false };
        ty.visit_with(&mut visitor);
    }

    fn report_wrong_site(&self, def_id: LocalDefId) {
        self.tcx.dcx().emit_err(errors::UnexportableItem {
            descr: self.tcx.def_descr(def_id.to_def_id()),
            span: self.tcx.def_span(def_id),
        });
    }

    fn check_visibility(&self, def_id: LocalDefId) {
        let visibilities = self.tcx.effective_visibilities(());
        if self.tcx.has_attr(def_id, sym::export) && !visibilities.is_directly_public(def_id) {
            let vis = visibilities.effective_vis(def_id).cloned().unwrap_or(
                EffectiveVisibility::from_vis(Visibility::Restricted(
                    self.tcx.parent_module_from_def_id(def_id).to_local_def_id(),
                )),
            );
            let vis = vis.at_level(Level::Direct);
            self.tcx.dcx().emit_err(errors::UnexportableItem {
                descr: &format!("item with {} visibility", vis.to_string(def_id, self.tcx)),
                span: self.tcx.def_span(def_id),
            });
            return;
        }
    }

    fn check_generics(&self, def_id: DefId) {
        let span = self.tcx.def_span(def_id);

        let generics = self.tcx.generics_of(def_id);
        if generics.requires_monomorphization(self.tcx) {
            self.tcx.dcx().emit_err(errors::UnexportableItem { descr: "generic item", span });
        }
    }
}

impl<'tcx> Visitor<'tcx> for CheckExportVisitor<'tcx> {
    type NestedFilter = nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let def_id = item.hir_id().owner.def_id;
        let span = item.span;
        self.check_visibility(def_id);

        match item.kind {
            hir::ItemKind::Mod(m) => self.visit_mod(m, span, item.hir_id()),
            hir::ItemKind::TyAlias(..) => self.check_alias(def_id.to_def_id(), span),
            hir::ItemKind::Fn(..) => self.check_fn(def_id.to_def_id()),
            hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) | hir::ItemKind::Union(..) => {
                self.check_ty(def_id.to_def_id(), span);
            }
            hir::ItemKind::Use(path, _) => {
                for res in &path.res {
                    match res {
                        Res::Def(DefKind::Fn, res_id) => self.check_fn(*res_id),
                        Res::Def(DefKind::Struct | DefKind::Union | DefKind::Enum, res_id) => {
                            self.check_ty(*res_id, span)
                        }
                        Res::Def(DefKind::TyAlias, res_id) => self.check_alias(*res_id, span),
                        _ => self.report_wrong_site(def_id),
                    }
                }
            }
            hir::ItemKind::Impl(impl_) if impl_.of_trait.is_none() => {
                self.check_generics(def_id.to_def_id());
                intravisit::walk_item(self, item);
            }
            _ => self.report_wrong_site(def_id),
        }
    }

    fn visit_impl_item(&mut self, item: &'tcx hir::ImplItem<'tcx>) {
        let def_id = item.hir_id().owner.def_id;
        self.check_visibility(def_id);

        match item.kind {
            hir::ImplItemKind::Fn(..) => self.check_fn(def_id.to_def_id()),
            hir::ImplItemKind::Type(..) => self.check_alias(def_id.to_def_id(), item.span),
            _ => self.report_wrong_site(def_id),
        }
    }
}

pub(crate) fn check_export<'tcx>(tcx: TyCtxt<'tcx>, hir_id: HirId) {
    let def_id = hir_id.owner.def_id;
    assert!(tcx.has_attr(def_id, sym::export));

    let mut visitor = CheckExportVisitor { tcx };

    match tcx.hir_owner_node(hir_id.owner) {
        hir::OwnerNode::Item(item) => visitor.visit_item(item),
        hir::OwnerNode::ForeignItem(_) | hir::OwnerNode::TraitItem(_) => {
            visitor.report_wrong_site(def_id)
        }
        hir::OwnerNode::ImplItem(item) => visitor.visit_impl_item(item),
        hir::OwnerNode::Crate(module) => {
            visitor.visit_mod(module, module.spans.inner_span, hir::CRATE_HIR_ID)
        }
        hir::OwnerNode::Synthetic => unreachable!(),
    }
}
