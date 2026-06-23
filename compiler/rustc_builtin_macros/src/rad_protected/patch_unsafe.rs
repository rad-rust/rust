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
    todo!();
}
