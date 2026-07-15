use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, symbol::Ident, sym, DUMMY_SP};
use thin_vec::thin_vec;

pub(crate) fn triplicate(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    _meta_item: &ast::MetaItem,
    mut item: Annotatable,
) -> Vec<Annotatable> {

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
