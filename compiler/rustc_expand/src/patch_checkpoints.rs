use rustc_ast as ast;
use rustc_ast::mut_visit::{self, MutVisitor};
use crate::base::ExtCtxt;
use rustc_span::{symbol::Ident, sym, DUMMY_SP};
use thin_vec::thin_vec;
use rustc_ast::visit::AssocCtxt;

pub fn patch_checkpoints(cx: &mut ExtCtxt<'_>, krate: &mut ast::Crate) {
    if cx.sess.opts.unstable_opts.force_unstable_if_unmarked {
        return;
    }
    let mut visitor = CheckpointRewriter { cx, active: false };
    visitor.visit_crate(krate);
}

struct DummyIdAssigner<'a, 'cx> {
    cx: &'a mut ExtCtxt<'cx>,
}

impl MutVisitor for DummyIdAssigner<'_, '_> {
    fn visit_id(&mut self, id: &mut ast::NodeId) {
        if *id == ast::DUMMY_NODE_ID {
            *id = self.cx.resolver.next_node_id();
        }
    }
}

struct CheckpointRewriter<'a, 'cx> {
    cx: &'a mut ExtCtxt<'cx>,
    active: bool,
}

impl MutVisitor for CheckpointRewriter<'_, '_> {
    fn visit_item(&mut self, item: &mut ast::Item) {
        let is_fn = matches!(item.kind, ast::ItemKind::Fn(_));
        let prev = self.active;

        if is_fn {
            self.active = has_rad_protected_mir(&item.attrs);
        }

        mut_visit::walk_item(self, item);

        self.active = prev;
    }

    fn visit_assoc_item(&mut self, item: &mut ast::AssocItem, ctxt: AssocCtxt) {
        let is_fn = matches!(item.kind, ast::AssocItemKind::Fn(_));
        let prev = self.active;

        if is_fn {
            self.active = has_rad_protected_mir(&item.attrs);
        }

        mut_visit::walk_assoc_item(self, item, ctxt);

        self.active = prev;
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        mut_visit::walk_expr(self, expr);

        if self.active && matches!(expr.kind, ast::ExprKind::Call(..) | ast::ExprKind::MethodCall(..)) {
            wrap_call_with_checkpoint(self.cx, expr);
        }
    }
}

fn has_rad_protected_mir(attrs: &[ast::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.has_name(sym::rad_protected_mir))
}

fn wrap_call_with_checkpoint(cx: &mut ExtCtxt<'_>, expr: &mut ast::Expr) {
    let span = expr.span;

    let checkpoint_call = cx.expr_call_global(
        DUMMY_SP,
        vec![
            Ident::new(sym::std, DUMMY_SP),
            Ident::new(sym::RadRustRuntime, DUMMY_SP),
            Ident::new(sym::__checkpoint, DUMMY_SP),
        ],
        thin_vec![],
    );

    let original = std::mem::replace(expr, *cx.expr_bool(DUMMY_SP, false));

    let checkpoint_stmt = cx.stmt_expr(checkpoint_call);
    let tail_stmt = cx.stmt_expr(Box::new(original));

    let mut block = cx.block(span, thin_vec![checkpoint_stmt, tail_stmt]);

    let mut assigner = DummyIdAssigner { cx };
    assigner.visit_block(&mut block);

    expr.id = ast::DUMMY_NODE_ID;
    expr.span = span;
    expr.kind = ast::ExprKind::Block(block, None);
    assigner.visit_id(&mut expr.id);
}
