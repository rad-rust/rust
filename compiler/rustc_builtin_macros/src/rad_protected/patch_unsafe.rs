use rustc_ast as ast;
use rustc_expand::base::ExtCtxt;

pub(crate) fn patch_unsafe_blocks(_cx: &ExtCtxt<'_>, _body: &mut ast::Block) {
    todo!();
}
