use crate::expand::AstFragment;
use ast::{
    Block, BlockCheckMode, Defaultness, Delegation, Fn, FnSig, Generics, Stmt, StmtKind, Ty,
};
use rustc_ast as ast;
use rustc_ast::mut_visit::*;
use rustc_ast::ptr::P;
use rustc_data_structures::base_n;
use rustc_data_structures::stable_hasher::{Hash128, StableHasher};
use rustc_span::{
    symbol::{kw, Ident},
    Span, Symbol,
};
use smallvec::{smallvec, SmallVec};
use std::hash::Hash;
use thin_vec::{thin_vec, ThinVec};

struct DelegationExpander;

struct Builder<'ast> {
    delegation: &'ast Delegation,
}

fn mk_unique_name(method_name: &str) -> Symbol {
    let mut hasher = StableHasher::new();
    method_name.hash(&mut hasher);
    let hash: Hash128 = hasher.finish();
    let generated = base_n::encode(hash.as_u128(), base_n::CASE_INSENSITIVE);
    Symbol::intern(generated.as_str())
}

impl<'ast> Builder<'ast> {
    fn new(delegation: &'ast Delegation) -> Self {
        Self { delegation }
    }

    fn span(&self) -> Span {
        self.delegation.span
    }

    fn mk_stmt(&self, kind: StmtKind) -> Stmt {
        Stmt { id: ast::DUMMY_NODE_ID, kind, span: self.span() }
    }

    fn mk_empty_header() -> ast::FnHeader {
        ast::FnHeader {
            unsafety: ast::Unsafe::No,
            asyncness: ast::Async::No,
            constness: ast::Const::No,
            ext: ast::Extern::None,
        }
    }

    fn mk_block(&self, stmts: ThinVec<Stmt>, rules: BlockCheckMode) -> Block {
        Block {
            stmts,
            id: ast::DUMMY_NODE_ID,
            rules,
            span: self.span(),
            tokens: None,
            could_be_bare_literal: false,
        }
    }

    fn mk_ty(&self, kind: ast::TyKind) -> P<Ty> {
        P(Ty { id: ast::DUMMY_NODE_ID, kind, span: self.span(), tokens: None })
    }

    fn mk_ident_pat(&mut self, ident: Ident) -> P<ast::Pat> {
        let pat = ast::Pat {
            id: ast::DUMMY_NODE_ID,
            kind: ast::PatKind::Ident(ast::BindingAnnotation::NONE, ident, None),
            span: self.span(),
            tokens: None,
        };
        P(pat)
    }

    fn mk_param(&mut self, ty: P<Ty>, pat: P<ast::Pat>) -> ast::Param {
        ast::Param {
            attrs: ast::AttrVec::default(),
            ty,
            pat,
            id: ast::DUMMY_NODE_ID,
            span: self.span(),
            is_placeholder: false,
        }
    }

    fn mk_main_expr(&mut self, method_ident: Ident) -> P<ast::Expr> {
        let args = thin_vec![P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            kind: ast::ExprKind::Underscore,
            span: self.span(),
            attrs: thin_vec![],
            tokens: None,
        })];
        let kind = ast::ExprKind::MethodCall(Box::new(ast::MethodCall {
            seg: ast::PathSegment { ident: method_ident, id: ast::DUMMY_NODE_ID, args: None },
            args,
            receiver: self.delegation.expr.clone(),
            span: self.span(),
        }));
        // append method call to expr
        P(ast::Expr {
            id: ast::DUMMY_NODE_ID,
            kind,
            span: self.delegation.span,
            attrs: thin_vec![],
            tokens: None,
        })
    }

    fn mk_proxy(&mut self, method_ident: Ident) -> ast::AssocItemKind {
        let header = Self::mk_empty_header();

        let pat = self.mk_ident_pat(Ident::new(kw::SelfLower, self.span()));
        let ty = self.mk_ty(ast::TyKind::ImplicitSelf);
        let param = self.mk_param(ty, pat);

        let decl =
            ast::FnDecl { inputs: thin_vec![param], output: ast::FnRetTy::Default(self.span()) };

        let expr = self.mk_main_expr(method_ident);
        let stmt = self.mk_stmt(StmtKind::Semi(expr));
        let mut stmts = ThinVec::new();
        stmts.push(stmt);
        let body = self.mk_block(stmts, BlockCheckMode::Default);
        let sig = FnSig { header, decl: P(decl), span: self.span() };

        let proxy = Fn {
            defaultness: Defaultness::Final,
            generics: Generics::default(),
            sig,
            body: Some(P(body)),
            delegation: ast::DelegationKind::Proxy,
        };

        ast::AssocItemKind::Fn(Box::new(proxy))
    }

    fn mk_gen(
        &mut self,
        method_ident: Ident,
        self_param: &Option<ast::Param>,
        assoc_proxy: Symbol,
    ) -> ast::AssocItemKind {
        let header = Self::mk_empty_header();
        let output = ast::FnRetTy::Ty(self.mk_ty(ast::TyKind::Infer));

        let expr = self.mk_main_expr(method_ident);
        let stmt = self.mk_stmt(StmtKind::Expr(expr));
        let mut stmts = ThinVec::new();
        stmts.push(stmt);
        let body = self.mk_block(stmts, BlockCheckMode::Default);

        let mut inputs = thin_vec![];
        let mut explicit_self = false;
        if let Some(self_param) = self_param {
            inputs.push(self_param.clone());
            explicit_self = true;
        }
        let decl = ast::FnDecl { inputs, output };
        let sig = FnSig { header, decl: P(decl), span: self.span() };

        let gen = Fn {
            defaultness: Defaultness::Final,
            generics: Generics::default(),
            sig,
            body: Some(P(body)),
            delegation: ast::DelegationKind::Gen { explicit_self, proxy: assoc_proxy },
        };
        ast::AssocItemKind::Fn(Box::new(gen))
    }
}

impl MutVisitor for DelegationExpander {
    fn flat_map_impl_item(&mut self, item: P<ast::AssocItem>) -> SmallVec<[P<ast::AssocItem>; 1]> {
        let ast::AssocItemKind::Delegation(ref del) = item.kind else {
            return smallvec![item];
        };
        let mut builder = Builder::new(del);

        let mut res = smallvec![];
        for delegation_item in &del.items {
            let proxy_kind = builder.mk_proxy(delegation_item.0);
            let proxy_name = mk_unique_name(delegation_item.0.name.as_str());
            let gen_kind = builder.mk_gen(delegation_item.0, &delegation_item.2, proxy_name);

            res.push(P(ast::AssocItem {
                attrs: thin_vec![],
                id: ast::DUMMY_NODE_ID,
                span: item.span,
                vis: item.vis.clone(),
                ident: Ident::new(proxy_name, item.span),
                kind: proxy_kind,
                tokens: None,
            }));

            let ident = delegation_item.1.unwrap_or(delegation_item.0);
            res.push(P(ast::AssocItem {
                attrs: item.attrs.clone(),
                id: ast::DUMMY_NODE_ID,
                span: item.span,
                vis: item.vis.clone(),
                ident,
                kind: gen_kind,
                tokens: None,
            }));
        }

        res
    }
}

pub fn delegate(mut fragment: AstFragment) -> AstFragment {
    fragment.mut_visit_with(&mut DelegationExpander);
    fragment
}
