use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::Visitor;
use rustc_hir::{self as hir, self, HirId};
use rustc_middle::hir::nested_filter;
use rustc_middle::middle::privacy::Level;
use rustc_middle::ty::TyCtxt;
use rustc_span::sym;
use rustc_target::spec::abi::Abi;

use crate::errors;

struct CheckExportVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> CheckExportVisitor<'tcx> {
    /// Only non-generic functions with a stable ABI (e.g. extern "C") are exportable.
    fn check_fn(&self, def_id: DefId) {
        let span = self.tcx.def_span(def_id);

        let generics = self.tcx.generics_of(def_id);
        if generics.requires_monomorphization(self.tcx) {
            self.tcx.dcx().emit_err(errors::UnexportableItem { descr: "generic item", span });
        }

        if !matches!(self.tcx.fn_sig(def_id).instantiate_identity().abi(), Abi::C { .. }) {
            self.tcx
                .dcx()
                .emit_err(errors::UnexportableItem { descr: "non \"C\" ABI function", span });
        }
    }

    /// Only structs/enums/unions with a stable representation (e.g. repr(i32) or repr(C)).
    /// are exportable.
    fn check_adt(&self, def_id: DefId) {
        let stable = self.tcx.get_attrs(def_id, sym::repr).any(|attr| {
            // FIXME: anything else?
            rustc_attr::find_repr_attrs(&self.tcx.sess, attr)
                .into_iter()
                .any(|r| matches!(r, rustc_attr::ReprC | rustc_attr::ReprInt(_)))
        });

        if !stable {
            self.tcx.dcx().emit_err(errors::UnexportableItem {
                descr: "type without stable representation",
                span: self.tcx.def_span(def_id),
            });
        }
    }

    fn report_wrong_site(&self, def_id: LocalDefId) {
        self.tcx.dcx().emit_err(errors::UnexportableItem {
            descr: self.tcx.def_descr(def_id.to_def_id()),
            span: self.tcx.def_span(def_id),
        });
    }
}

impl<'tcx> Visitor<'tcx> for CheckExportVisitor<'tcx> {
    type NestedFilter = nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let def_id = item.hir_id().owner.def_id;
        let visibilities = self.tcx.effective_visibilities(());
        if self.tcx.has_attr(def_id, sym::export)
            && !visibilities.is_public_at_level(def_id, Level::Direct)
        {
            let vis = visibilities.effective_vis(def_id).unwrap().at_level(Level::Direct);
            self.tcx.dcx().emit_err(errors::UnexportableItem {
                descr: &format!("item with {} visibility", vis.to_string(def_id, self.tcx)),
                span: self.tcx.def_span(def_id),
            });
            return;
        }

        match item.kind {
            hir::ItemKind::Mod(m) => self.visit_mod(m, item.span, item.hir_id()),
            hir::ItemKind::TyAlias(..) => {}
            hir::ItemKind::Fn(..) => self.check_fn(def_id.to_def_id()),
            hir::ItemKind::Struct(..) | hir::ItemKind::Enum(..) | hir::ItemKind::Union(..) => {
                self.check_adt(def_id.to_def_id());
            }
            hir::ItemKind::Use(path, _) => {
                for res in &path.res {
                    match res {
                        Res::Def(DefKind::Fn, res_id) => self.check_fn(*res_id),
                        Res::Def(DefKind::Struct | DefKind::Union | DefKind::Enum, res_id) => {
                            self.check_adt(*res_id)
                        }
                        _ => self.report_wrong_site(def_id),
                    }
                }
            }
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
        hir::OwnerNode::ImplItem(_impl_item) => {}
        hir::OwnerNode::Crate(module) => {
            visitor.visit_mod(module, module.spans.inner_span, hir::CRATE_HIR_ID)
        }
        hir::OwnerNode::Synthetic => unreachable!(),
    }
}
