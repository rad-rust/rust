use rustc_ast as ast;
use rustc_expand::base::{Annotatable, ExtCtxt};
use rustc_span::{Span, symbol::Ident, sym, Symbol, DUMMY_SP};
use thin_vec::{thin_vec, ThinVec};
use rustc_ast::{MetaItemInner, FnSig};
use crate::rad_protected::patch_unsafe::patch_unsafe_blocks;

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

    let mut func_body = match &func.body {
        Some(b) => b.clone(),
        None => {
            cx.dcx().span_err(span, "`#[rad_protected]` can only be applied to functions with a body");
            return vec![item];
        }
    };

    patch_unsafe_blocks(cx, &mut func_body);

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
    
    let make_inner_fn_stmt = |suffix_num: usize| {

        let mut sig = func.sig.clone();
        add_mutex_param(cx, &mut sig);

        let inner_fn = ast::Fn {
            defaultness: ast::Defaultness::Implicit,
            ident: inner_fn_ident(func.ident.name, suffix_num),
            generics: func.generics.clone(),
            sig,
            contract: None,
            define_opaque: None,
            body: Some(func_body.clone()),
            eii_impls: thin_vec![]
        };

        let inner_attrs = 
            if triplicate_body {
                let inline_attr = cx.attr_nested_word(sym::inline, sym::never, DUMMY_SP);
                let link_section_attr = cx.attr_name_value_str_unsafe(
                    sym::link_section, 
                    Symbol::intern(&format!(".text.{}_{}", func.ident.name, suffix_num)), 
                    DUMMY_SP
                );
                thin_vec![inline_attr, link_section_attr]
                
            } else {
                thin_vec![]
            };

        cx.stmt_item(DUMMY_SP, cx.item(
            DUMMY_SP, 
            inner_attrs, 
            ast::ItemKind::Fn(Box::new(inner_fn))
        ))
    };

    let call_args: ThinVec<_> = func.sig.decl.inputs.iter().filter_map(|param| {
        match &param.pat.kind {
            ast::PatKind::Ident(_, ident, _) => Some(cx.expr_ident(param.pat.span, *ident)),
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
        let fn_ident = inner_fn_ident(func.ident.name, if triplicate_body { suffix_num } else { 1 });

        let multithreading_clone_expr = cx.expr_method_call(
            DUMMY_SP,
            cx.expr_ident(DUMMY_SP, multithreading_ident()),
            Ident::new(sym::clone, DUMMY_SP),
            thin_vec![],
        );

        let m_ident = Ident::from_str_and_span("m", DUMMY_SP);
        let local_stmt = cx.stmt_let(
            DUMMY_SP,
            false,
            m_ident,
            multithreading_clone_expr,
        );

        let mut call_args = call_args.clone();
        call_args.push(cx.expr_ident(DUMMY_SP, m_ident));

        let call = cx.expr_call_ident(DUMMY_SP, fn_ident, call_args);

        let body_block = cx.expr_block(cx.block(DUMMY_SP, thin_vec![
            cx.stmt_expr(call)
        ]));

        let mut closure_expr = cx.lambda(DUMMY_SP, vec![], body_block);
        
        if let ast::ExprKind::Closure(ref mut closure) = closure_expr.kind {
            closure.capture_clause = ast::CaptureBy::Value { move_kw: DUMMY_SP };
        }

        cx.expr_block(cx.block(DUMMY_SP, thin_vec![
            local_stmt,
            cx.stmt_expr(closure_expr)
        ]))
    };
    
    const NUM_DUPLICATES: usize = 3;

    let mut wrapper_stmts: ThinVec<ast::Stmt> = thin_vec![];
    
    wrapper_stmts.extend((1..=if triplicate_body { NUM_DUPLICATES } else { 1 }).map(make_inner_fn_stmt));

    let multithreading_use_item = {
        let path = cx.path_global(DUMMY_SP, rad_protected_path(false, vec![
            Ident::from_str_and_span("Multithreading", DUMMY_SP),
        ]));

        let use_tree = ast::UseTree {
            prefix: path,
            kind: ast::UseTreeKind::Simple(None),
            span: DUMMY_SP,
        };

        cx.stmt_item(DUMMY_SP, cx.item(
            DUMMY_SP,
            thin_vec![],
            ast::ItemKind::Use(use_tree),
        ))
    };
    wrapper_stmts.push(multithreading_use_item);

    let multithreading_init_stmt = {
        let multithreading_init = cx.expr_call_global(
            DUMMY_SP,
            rad_protected_path(true, vec![
                multithreading_impl_ty_ident(),
                Ident::new(sym::new, DUMMY_SP),
            ]),
            thin_vec![
                cx.expr_usize(DUMMY_SP, NUM_DUPLICATES)
            ],
        );

        cx.stmt_let(
            DUMMY_SP,
            false,
            multithreading_ident(),
            multithreading_init,
        )
    };
    wrapper_stmts.push(multithreading_init_stmt);

    let run_triple_stmt = { 
        let run_triple_path = cx.path_global(
            DUMMY_SP,
            rad_protected_path(true, vec![
                multithreading_impl_ty_ident(),
                Ident::from_str_and_span("run_triple", DUMMY_SP)
            ]),
        );

        let run_triple_args: ThinVec<_> = (1..=NUM_DUPLICATES).map(make_call_expr).collect();

        cx.stmt_expr(cx.expr_call(
            DUMMY_SP, 
            cx.expr_path(run_triple_path), run_triple_args
        ))
    };
    wrapper_stmts.push(run_triple_stmt);

    let wrapper_body = cx.block(DUMMY_SP, wrapper_stmts);

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

    let mir_attr = cx.attr_word(sym::rad_protected_mir, DUMMY_SP);
    
    let mut wrapper = cx.item(DUMMY_SP, thin_vec![mir_attr], ast::ItemKind::Fn(Box::new(wrapper_fn)));
    wrapper.vis = vis.clone();

    vec![Annotatable::Item(wrapper)]
}

fn add_mutex_param(cx: &ExtCtxt<'_>, sig: &mut FnSig) {
    sig.decl.inputs.push(cx.param(
        DUMMY_SP,
        multithreading_ident(), 
        cx.ty_path(cx.path_global(DUMMY_SP, rad_protected_path(true, vec![
                multithreading_impl_ty_ident(),
        ])))
    ));
}

fn rad_protected_path(_impl_path: bool, tail: Vec<Ident>) -> Vec<Ident> {
    let mut path = vec![
        Ident::new(if _impl_path { sym::std } else { sym::core }, DUMMY_SP),
        Ident::new(sym::rad_protected, DUMMY_SP),
    ];

    path.extend(tail);
    path
}

fn inner_fn_ident(name: Symbol, suffix_num: usize) -> Ident {
    Ident::from_str_and_span(
        &format!("__{}_{}", name, suffix_num), 
        DUMMY_SP
    )
}

fn multithreading_ident() -> Ident {
    Ident::from_str_and_span("multithreading", DUMMY_SP)
}

fn multithreading_impl_ty_ident() -> Ident {
    Ident::from_str_and_span("StdMultithreading", DUMMY_SP)
}
