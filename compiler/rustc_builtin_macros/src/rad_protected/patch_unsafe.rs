use rustc_ast as ast;
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_expand::base::ExtCtxt;
use rustc_span::{symbol::Ident, DUMMY_SP};
use thin_vec::thin_vec;

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
                patch_unsafe_block(self.cx, block);
                return;
            }
        }

        mut_visit::walk_expr(self, expr);
    }
}

fn patch_unsafe_block(cx: &ExtCtxt<'_>, block: &mut ast::Block) {

    let multithreading_method_call = |name: &str| {
        let multithreading_ident = Ident::from_str_and_span("_multithreading", DUMMY_SP);
        let method_name_ident = Ident::from_str_and_span(name, DUMMY_SP);

        cx.expr_method_call(
            DUMMY_SP,
            cx.expr_ident(DUMMY_SP, multithreading_ident),
            method_name_ident,
            thin_vec![],
        )
    };

    let enter_call = multithreading_method_call("enter_critical_section");
    let exit_call = multithreading_method_call("exit_critical_section");

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
