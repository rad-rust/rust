use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, symbol::Ident, sym, DUMMY_SP};
use thin_vec::thin_vec;
use super::parse_attr_opts::parse_attr_opts;

pub(crate) fn triplicate(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    meta_item: &ast::MetaItem,
    mut item: Annotatable,
) -> Vec<Annotatable> {

    let Some(opts) = parse_attr_opts(cx, meta_item) else {
        return vec![item];
    };

    if opts.triplicate_unsafe() {
        let valid = match &mut item {
            Annotatable::Expr(expr)
                if matches!(&expr.kind, ast::ExprKind::Block(block, _)
                    if matches!(block.rules, ast::BlockCheckMode::Unsafe(_))
                ) => {
                    expr.attrs.push(cx.attr_nested_word(
                        sym::rad_protected_mir,
                        sym::triplicate_unsafe,
                        DUMMY_SP,
                    ));
                    true
                }
            _ => false,
        };

        if !valid {
            cx.dcx().span_err(
                span,
                "`#[rad_protected(triplicate_unsafe)]` can only be applied to `unsafe` blocks",
            );
        }

        return vec![item];
    }

    let Annotatable::Item(box ast::Item {
        kind: ast::ItemKind::Fn(box ref mut func),
        ..
    }) = item else {
        cx.dcx().span_err(span, "`#[rad_protected]` can only be applied to functions");
        return vec![item];
    };

    let func_body = match &mut func.body {
        Some(b) => b,
        None => {
            cx.dcx().span_err(span, "`#[rad_protected]` can only be applied to functions with a body");
            return vec![item];
        }
    };

    func_body.stmts.insert(0, cx.stmt_let(
        DUMMY_SP,
        false,
        Ident::new(sym::__guard, DUMMY_SP),
        cx.expr_call_global(
            DUMMY_SP,
            vec![
                Ident::new(sym::std, DUMMY_SP),
                Ident::new(sym::RadRustRuntime, DUMMY_SP),
                Ident::new(sym::triplicate_process, DUMMY_SP),
            ], 
            thin_vec![]
        )
    ));

    vec![item]
}
