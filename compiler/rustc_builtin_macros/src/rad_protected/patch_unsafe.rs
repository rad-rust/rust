use rustc_ast as ast;
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_expand::base::ExtCtxt;
use rustc_span::{symbol::Ident, Symbol, sym, DUMMY_SP};
use thin_vec::{ThinVec, thin_vec};
use rustc_ast::MetaItemInner;

pub(crate) fn patch_unsafe_blocks(cx: &ExtCtxt<'_>, body: &mut ast::Block) {
    let mut visitor = UnsafeBlockRewriter { cx };
    visitor.visit_block(body);
}

struct UnsafeBlockRewriter<'a, 'cx> {
    cx: &'a ExtCtxt<'cx>,
}

impl MutVisitor for UnsafeBlockRewriter<'_, '_> {
    fn visit_expr(&mut self, expr: &mut ast::Expr) {

        if let ast::ExprKind::Block(block, _) = &mut expr.kind {
            if matches!(block.rules, ast::BlockCheckMode::Unsafe(_)) {

                if !skip_patch(&expr.attrs) {
                    patch_unsafe_block(self.cx, block);
                }
                return;
            }
        }

        mut_visit::walk_expr(self, expr);
    }
}

fn patch_unsafe_block(cx: &ExtCtxt<'_>, block: &mut ast::Block) {

    let runtime_method_call = |name: Symbol| {
        cx.expr_call_global(
            DUMMY_SP,
            vec![
                Ident::new(sym::std, DUMMY_SP),
                Ident::new(sym::RadRustRuntime, DUMMY_SP),
                Ident::new(name, DUMMY_SP),
            ], 
            thin_vec![]
        )
    };

    let enter_call = runtime_method_call(sym::enter_critical_section);
    let exit_call = runtime_method_call(sym::exit_critical_section);

    let if_stmt = cx.stmt_expr(cx.expr_if(
        DUMMY_SP,
        enter_call,
        cx.expr_block(cx.block(block.span, block.stmts.clone())),
        None,
    ));
    
    let exit_call_stmt = cx.stmt_expr(exit_call);

    block.stmts = thin_vec![
        if_stmt,
        exit_call_stmt
    ];
}

fn skip_patch(attrs: &ThinVec<ast::Attribute>) -> bool {
    attrs.iter().any(|attr| {         
        let Some(meta) = attr.meta() else {
            return false;
        };

        if !meta.has_name(sym::rad_protected) {
            return false;
        }

        match &meta.kind {
            ast::MetaItemKind::List(items) => items.iter().any(|item| {
                matches!(item, MetaItemInner::MetaItem(mi) if mi.has_name(sym::triplicate_unsafe))
            }),
            _ => false,
        }
    })
}
