use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, sym, DUMMY_SP};
use super::parse_attr_opts::parse_attr_opts;

pub(crate) fn validate_attr(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    meta_item: &ast::MetaItem,
    mut item: Annotatable,
) -> Vec<Annotatable> {

    let Some(opts) = parse_attr_opts(cx, meta_item) else {
        return vec![item];
    };

    if opts.unguarded_unsafe() {
        let valid = match &mut item {
            Annotatable::Expr(expr)
                if matches!(&expr.kind, ast::ExprKind::Block(block, _)
                    if matches!(block.rules, ast::BlockCheckMode::Unsafe(_))
                ) => {
                    expr.attrs.push(cx.attr_nested_word(
                        sym::rad_protected,
                        sym::unguarded_unsafe,
                        DUMMY_SP,
                    ));
                    true
                }
            _ => false,
        };

        if !valid {
            cx.dcx().span_err(
                span,
                "`#[rad_protected(unguarded_unsafe)]` can only be applied to `unsafe` blocks",
            );
        }
    } 
    else {
        cx.dcx().span_err(
            span,
            "`#[rad_protected(..)]` can only be used with options",
        );
    }
    
    return vec![item];
}
