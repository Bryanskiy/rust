// TODO: move to another crate?.
// TODO: should the interface be printed without `Crate` deneration? (only pp).
// TODO: generated  rate shouldn't be visible outside of this module as it contains
//       broken spans, id's.
// TODO: feature gate for `crate-type=rdylib`?
// TODO: all fns in form: extern "crabi" { fn foo(); ... }

use rustc_ast as ast;
use rustc_ast::ptr::P;
use rustc_ast::visit::Visitor;
use rustc_ast::{Block, Crate, Expr, ExprKind, Fn, Item, ItemKind, ModSpans, Stmt, DUMMY_NODE_ID};
use rustc_span::DUMMY_SP;
use thin_vec::{thin_vec, ThinVec};

struct CrateGen {
    krate: Crate,
}

impl CrateGen {
    fn new() -> CrateGen {
        CrateGen {
            krate: Crate {
                attrs: thin_vec![],
                items: thin_vec![],
                spans: ModSpans { inject_use_span: DUMMY_SP, inner_span: DUMMY_SP },
                is_placeholder: false,
                id: DUMMY_NODE_ID,
            },
        }
    }
}

// TODO: `#[extern]` check
// TODO: other items
impl Visitor<'_> for CrateGen {
    fn visit_item(&mut self, item: &'_ Item) {
        let ItemKind::Fn(fn_) = &item.kind else {
            return;
        };
        let empty_block = mk_block(thin_vec![]);
        let expr = Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::Loop(P(empty_block), None, DUMMY_SP),
            span: DUMMY_SP,
            attrs: thin_vec![],
            tokens: None,
        };

        let stmt =
            Stmt { kind: rustc_ast::StmtKind::Expr(P(expr)), id: DUMMY_NODE_ID, span: DUMMY_SP };

        let fn_block = mk_block(thin_vec![stmt]);

        let new_fn = Fn {
            body: Some(P(fn_block)),
            defaultness: rustc_ast::Defaultness::Final,
            generics: fn_.generics.clone(),
            sig: fn_.sig.clone(),
        };

        let item_kind = ItemKind::Fn(Box::new(new_fn));

        let item = Item {
            attrs: item.attrs.clone(), // TODO: which attrs should be copied?
            id: DUMMY_NODE_ID,
            span: item.span,
            vis: item.vis.clone(),
            ident: item.ident,
            kind: item_kind,
            tokens: None,
        };

        self.krate.items.push(P(item));
    }
}

#[inline]
fn mk_block(stmts: ThinVec<Stmt>) -> Block {
    Block {
        stmts,
        id: DUMMY_NODE_ID,
        rules: rustc_ast::BlockCheckMode::Default,
        span: DUMMY_SP,
        tokens: None,
        could_be_bare_literal: false,
    }
}

pub fn gen_crate(krate: &'_ Crate) -> Crate {
    let mut crate_gen = CrateGen::new();
    ast::visit::walk_crate(&mut crate_gen, krate);
    crate_gen.krate
}
