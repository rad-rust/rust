use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, symbol::Ident, sym, Symbol};
use thin_vec::{thin_vec, ThinVec};
use rustc_ast::MetaItemInner;

pub(crate) fn triplicate(
    cx: &mut ExtCtxt<'_>,
    span: Span,
    meta_item: &ast::MetaItem,
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

    let attr_opts: ThinVec<MetaItemInner> = match meta_item.kind {
        ast::MetaItemKind::List(ref vec) => vec.clone(),
        ast::MetaItemKind::Word => thin_vec![],
        _ => {
            cx.dcx().span_err(meta_item.span, "unsupported options kind in `#[rad_protected]`");
            thin_vec![]
        }
    };
    
    let mut triplicate_body = true;

    for opt in attr_opts {
        match opt {
            MetaItemInner::MetaItem(opt) if opt.has_name(sym::no_triplicate_body) => {
                triplicate_body = false;
            }
            _ => {
                cx.dcx().span_err(meta_item.span, "unsupported option in `#[rad_protected]`");
            }
        }
    }

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

        let inner_attrs = 
            if triplicate_body {
                let inline_attr = cx.attr_nested_word(sym::inline, sym::never, span);
                let link_section_attr = cx.attr_name_value_str_unsafe(
                    sym::link_section, 
                    Symbol::intern(&format!(".text.{}_{}", func.ident.name, suffix_num)), 
                    span
                );
                thin_vec![inline_attr, link_section_attr]
                
            } else {
                thin_vec![]
            };

        let item = cx.item(span, inner_attrs, ast::ItemKind::Fn(Box::new(inner_fn)));
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


    let make_call_expr = |suffix_num: usize| {
        cx.expr_call_ident(span, make_ident(if triplicate_body { suffix_num } else { 1 }), call_args.clone())
    };

    const NUM_DUPLICATES: usize = 3;

    let mut wrapper_stmts: ThinVec<ast::Stmt> = thin_vec![];
    
    wrapper_stmts.extend((1..=if triplicate_body { NUM_DUPLICATES } else { 1 }).map(make_inner_fn_stmt));

    let vote_path = cx.path_global(
        span,
        vec![
            Ident::new(sym::std, span), 
            Ident::new(sym::rad_protected, span), 
            Ident::from_str_and_span("vote", span)
        ],
    );

    let vote_args: ThinVec<_> = (1..=NUM_DUPLICATES).map(make_call_expr).collect();

    let vote_expr = cx.expr_path(vote_path);
    let vote_call = cx.expr_call(span, vote_expr, vote_args);
    let vote_stmt = cx.stmt_expr(vote_call);

    wrapper_stmts.push(vote_stmt);

    let wrapper_body = cx.block(span, wrapper_stmts);

    let wrapper_fn = ast::Fn {
        defaultness: func.defaultness,
        ident: func.ident,
        sig: func.sig.clone(),
        generics: func.generics.clone(),
        body: Some(wrapper_body),
        contract: func.contract.clone(),
        define_opaque: func.define_opaque.clone(),
        eii_impls: func.eii_impls.clone()
    };

    let mir_attr = cx.attr_word(sym::rad_protected_mir, span);
    
    let mut wrapper = cx.item(span, thin_vec![mir_attr], ast::ItemKind::Fn(Box::new(wrapper_fn)));
    wrapper.vis = vis.clone();

    vec![Annotatable::Item(wrapper)]
}
