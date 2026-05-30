use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, symbol::Ident, sym};
use thin_vec::{thin_vec, ThinVec};

pub(crate) fn triplicate(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    _meta_item: &ast::MetaItem,
    item: Annotatable,
) -> Vec<Annotatable> {

    let Annotatable::Item(box ast::Item {
        kind: ast::ItemKind::Fn(box ref func),
        ref vis,
        ..
    }) = item else {
        cx.dcx().span_err(span, "`#[rad_protected]` can only be applied to functions");
        return vec![item];
    };

    let func_body = match &func.body {
        Some(b) => b,
        None => {
            cx.dcx().span_err(span, "`#[rad_protected]` can only be applied to functions with a body");
            return vec![item];
        }
    };

    let make_ident = |suffix_num: usize| {
        Ident::from_str_and_span(
            &format!("__{}_{}", func.ident.name, suffix_num), 
            span
        )
    };
    
    let make_inner_fn_stmt = |suffix_num: usize| {

        let inner_fn = ast::Fn {
            defaultness: ast::Defaultness::Implicit,
            ident: make_ident(suffix_num),
            generics: func.generics.clone(),
            sig: func.sig.clone(),
            contract: None,
            define_opaque: None,
            body: Some(func_body.clone()),
            eii_impls: thin_vec![]
        };

        let item = cx.item(span, ast::AttrVec::new(), ast::ItemKind::Fn(Box::new(inner_fn)));
        cx.stmt_item(span, item)
    };

    let call_args: ThinVec<_> = func.sig.decl.inputs.iter().filter_map(|param| {
        match &param.pat.kind {
            ast::PatKind::Ident(_, ident, _) => Some(cx.expr_ident(span, *ident)),
            _ => {
                cx.dcx().span_err(
                    param.pat.span, 
                    "unsupported parameter pattern in `#[rad_protected]`"
                );
                None
            }
        }
    }).collect();

    let make_call_stmt = |suffix_num: usize| {
        let call = cx.expr_call_ident(span, make_ident(suffix_num), call_args.clone());

        cx.stmt_semi(call)
    };

    const NUM_DUPLICATES: usize = 3;

    let mut wrapper_stmts: ThinVec<ast::Stmt> = thin_vec![];
    
    wrapper_stmts.extend((1..=NUM_DUPLICATES).map(make_inner_fn_stmt));
    wrapper_stmts.extend((1..=NUM_DUPLICATES).map(make_call_stmt));

    let wrapper_body = cx.block(span, wrapper_stmts);

    let mut wrapper_fn = ast::Fn {
        defaultness: func.defaultness,
        ident: func.ident,
        sig: func.sig.clone(),
        generics: func.generics.clone(),
        body: Some(wrapper_body),
        contract: func.contract.clone(),
        define_opaque: func.define_opaque.clone(),
        eii_impls: func.eii_impls.clone()
    };

    // The return type is temporarily the unit type until voting is implemented
    wrapper_fn.sig.decl.output = ast::FnRetTy::Default(span);

    let mir_attr = cx.attr_word(sym::rad_protected_mir, span);
    
    let mut wrapper = cx.item(span, thin_vec![mir_attr], ast::ItemKind::Fn(Box::new(wrapper_fn)));
    wrapper.vis = vis.clone();

    vec![Annotatable::Item(wrapper)]
}
