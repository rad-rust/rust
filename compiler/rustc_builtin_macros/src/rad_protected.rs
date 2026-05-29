use rustc_ast::{self as ast};
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::Span;

pub(crate) fn triplicate(
    _cx: &mut ExtCtxt<'_>,
    _span: Span,
    _meta_item: &ast::MetaItem,
    _item: Annotatable,
) -> Vec<Annotatable> {
    // TODO:
    todo!()
}
