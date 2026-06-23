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

    let make_ident = |suffix_num: usize| {
        Ident::from_str_and_span(
            &format!("__{}_{}", func.ident.name, suffix_num), 
            span
        )
    };
    
    let make_inner_fn_stmt = |suffix_num: usize| {

        let mut sig = func.sig.clone();
        add_mutex_param(&mut sig);

        let inner_fn = ast::Fn {
            defaultness: ast::Defaultness::Implicit,
            ident: make_ident(suffix_num),
            generics: func.generics.clone(),
            sig,
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
        let fn_ident = make_ident(if triplicate_body { suffix_num } else { 1 });

        let multithreading_clone_expr = cx.expr_method_call(
            span,
            cx.expr_ident(span, Ident::from_str_and_span("multithreading", span)),
            Ident::new(sym::clone, span),
            thin_vec![],
        );

        let m_ident = Ident::from_str_and_span("m", span);
        let local_stmt = cx.stmt_let(
            span,
            false,
            m_ident,
            multithreading_clone_expr,
        );

        let mut call_args = call_args.clone();
        call_args.push(cx.expr_ident(span, m_ident));

        let call = cx.expr_call_ident(span, fn_ident, call_args);

        let body_block = cx.expr_block(cx.block(span, thin_vec![
            cx.stmt_expr(call)
        ]));

        let mut closure_expr = cx.lambda(span, vec![], body_block);
        
        if let ast::ExprKind::Closure(ref mut closure) = closure_expr.kind {
            closure.capture_clause = ast::CaptureBy::Value { move_kw: span };
        }

        cx.expr_block(cx.block(span, thin_vec![
            local_stmt,
            cx.stmt_expr(closure_expr)
        ]))
    };
    
    const NUM_DUPLICATES: usize = 3;

    let mut wrapper_stmts: ThinVec<ast::Stmt> = thin_vec![];

    let multithreading_use_item = {
        let path = ast::Path {
            span,
            segments: thin_vec![
                ast::PathSegment::from_ident(Ident::new(sym::std, span)),
                ast::PathSegment::from_ident(Ident::new(sym::rad_protected, span)),
                ast::PathSegment::from_ident(Ident::from_str_and_span("Multithreading", span)),
            ],
            tokens: None,
        };

        let use_tree = ast::UseTree {
            prefix: path,
            kind: ast::UseTreeKind::Simple(None),
            span,
        };

        let use_item = cx.item(
            span,
            ThinVec::new(),
            ast::ItemKind::Use(use_tree),
        );

        cx.stmt_item(span, use_item)
    };
    wrapper_stmts.push(multithreading_use_item);


    let multithreading_ident = Ident::from_str_and_span("multithreading", span);

    let multithreading_init = cx.expr_call(
        span,
        cx.expr_path(cx.path_global(
            span,
            vec![
                Ident::new(sym::std, span),
                Ident::new(sym::rad_protected, span),
                Ident::from_str_and_span("StdMultithreading", span),
                Ident::new(sym::new, span),
            ],
        )),
        thin_vec![
            cx.expr_usize(span, NUM_DUPLICATES)
        ],
    );

    let multithreading_stmt = cx.stmt_let(
        span,
        false,
        multithreading_ident,
        multithreading_init,
    );

    wrapper_stmts.push(multithreading_stmt);
    
    wrapper_stmts.extend((1..=if triplicate_body { NUM_DUPLICATES } else { 1 }).map(make_inner_fn_stmt));

    let run_triple_path = cx.path_global(
        span,
        vec![
            Ident::new(sym::std, span), 
            Ident::new(sym::rad_protected, span), 
            Ident::from_str_and_span("StdMultithreading", span),
            Ident::from_str_and_span("run_triple", span)
        ],
    );

    let run_triple_args: ThinVec<_> = (1..=NUM_DUPLICATES).map(make_call_expr).collect();

    let run_triple_expr = cx.expr_path(run_triple_path);
    let run_triple_call = cx.expr_call(span, run_triple_expr, run_triple_args);
    let run_triple_stmt = cx.stmt_expr(run_triple_call);

    wrapper_stmts.push(run_triple_stmt);

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

fn add_mutex_param(sig: &mut FnSig) {
    sig.decl.inputs.push(ast::Param {
        attrs: Default::default(),

        pat: Box::new(ast::Pat {
            id: ast::DUMMY_NODE_ID,
            kind: ast::PatKind::Ident(
                ast::BindingMode::NONE,
                Ident::from_str_and_span("multithreading", DUMMY_SP),
                None,
            ),
            span: DUMMY_SP,
            tokens: None,
        }),

        ty: Box::new(ast::Ty {
            id: ast::DUMMY_NODE_ID,
            kind: ast::TyKind::Path(
                None,
                ast::Path {
                    span: DUMMY_SP,
                    segments: thin_vec![
                        ast::PathSegment {
                            ident: Ident::new(sym::std, DUMMY_SP), 
                            id: ast::DUMMY_NODE_ID,
                            args: None,
                        },
                        ast::PathSegment {
                            ident: Ident::new(sym::rad_protected, DUMMY_SP), 
                            id: ast::DUMMY_NODE_ID,
                            args: None,
                        },
                        ast::PathSegment {
                            ident: Ident::from_str_and_span("StdMultithreading", DUMMY_SP),
                            id: ast::DUMMY_NODE_ID,
                            args: None,
                        },
                    ],
                    tokens: None,
                },
            ),
            span: DUMMY_SP,
            tokens: None,
        }),

        id: ast::DUMMY_NODE_ID,
        span: DUMMY_SP,
        is_placeholder: false,
    });
}
