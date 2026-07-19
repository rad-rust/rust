use rustc_ast as ast;
use rustc_ast::mut_visit::{self, MutVisitor};
use crate::base::ExtCtxt;
use rustc_span::{symbol::Ident, Symbol, sym, DUMMY_SP};
use thin_vec::{ThinVec, thin_vec};
use rustc_ast::MetaItemInner;

pub fn patch_unsafe_blocks(cx: &mut ExtCtxt<'_>, krate: &mut ast::Crate) {
    if cx.sess.opts.unstable_opts.force_unstable_if_unmarked {
        return;
    }
    let mut visitor = UnsafeBlockRewriter { cx };
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

struct UnsafeBlockRewriter<'a, 'cx> {
    cx: &'a mut ExtCtxt<'cx>,
}

impl MutVisitor for UnsafeBlockRewriter<'_, '_> {
    fn visit_expr(&mut self, expr: &mut ast::Expr) {

        if let ast::ExprKind::Block(block, _) = &mut expr.kind {
            if matches!(block.rules, ast::BlockCheckMode::Unsafe(_)) {

                if !skip_patch(&mut expr.attrs) {
                    patch_unsafe_block(self.cx, block);
                }
                return;
            }
        }

        mut_visit::walk_expr(self, expr);
    }
}

fn patch_unsafe_block(cx: &mut ExtCtxt<'_>, block: &mut ast::Block) {
    let runtime_method_call = |cx: &mut ExtCtxt<'_>, name: Symbol| {
        cx.expr_call_global(
            DUMMY_SP,
            vec![
                Ident::new(sym::std, DUMMY_SP),
                Ident::new(sym::RadRustRuntime, DUMMY_SP),
                Ident::new(name, DUMMY_SP),
            ],
            thin_vec![],
        )
    };

    let enter_call = runtime_method_call(cx, sym::enter_critical_section);
    let exit_call = runtime_method_call(cx, sym::exit_critical_section);

    let inner_block = cx.block(block.span, block.stmts.clone());
    let if_stmt = cx.stmt_expr(cx.expr_if(DUMMY_SP, 
        enter_call, 
        cx.expr_block(inner_block), 
        None
    ));
    let exit_call_stmt = cx.stmt_expr(exit_call);

    let mut assigner = DummyIdAssigner { cx };
    let if_stmt = assign_stmt(&mut assigner, if_stmt);
    let exit_call_stmt = assign_stmt(&mut assigner, exit_call_stmt);

    block.stmts = thin_vec![if_stmt, exit_call_stmt];
}

fn skip_patch(attrs: &mut ThinVec<ast::Attribute>) -> bool {
    let mut removed = false;

    attrs.retain(|attr| {
        let keep = !attr.meta().is_some_and(is_skip_attr);

        if !keep {
            removed = true;
        }
        keep
    });

    removed
}

fn is_skip_attr(meta: ast::MetaItem) -> bool {
    if !meta.has_name(sym::rad_protected_mir) {
        return false;
    }

    let ast::MetaItemKind::List(items) = &meta.kind else {
        return false;
    };

    items.iter().any(|item| {
        matches!(item, MetaItemInner::MetaItem(mi) if mi.has_name(sym::triplicate_unsafe))
    })
}

fn assign_stmt(assigner: &mut DummyIdAssigner<'_, '_>, stmt: ast::Stmt) -> ast::Stmt {
    assigner
        .flat_map_stmt(stmt)
        .into_iter()
        .next()
        .expect("statement unexpectedly removed")
}
