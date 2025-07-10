// In your proc-macro crate's src/lib.rs

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, quote}; // format_ident is key here
use syn::parenthesized;
use syn::parse::Parser;
use syn::punctuated::Punctuated;
use syn::token::Paren;
use syn::{
    parse::{Parse, ParseStream, Result},
    parse_macro_input,
    token,
    Expr,
    Ident,
    Lit,
    LitInt,
    LitStr, // LitStr might not be needed if FunApp changed
    Token,
};
use utils::ereturn_if;

// Counter for generating unique temporary variable names
static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);

use super::parser::*;

fn generate_banged_expr_tokens(b: BangedContent) -> proc_macro2::TokenStream {
    match b {
        BangedContent::Lit(lit) => quote! { #lit },
        BangedContent::Ident(ident) => quote! { #ident.clone() },
        BangedContent::Expr(expr) => quote! { (#expr) }, // Parenthesize expr just in case
    }
}

fn generate_var_index_expr_tokens(v_idx: &VarIndex) -> proc_macro2::TokenStream {
    match v_idx {
        VarIndex::Lit(lit_int) => quote! { #lit_int },
        VarIndex::Expr(expr) => quote! { (#expr) }, // Parenthesize expr
        VarIndex::Ident(ident) => quote! { #ident.clone() },
    }
}

fn generate_args(items: ArgsVec) -> proc_macro2::TokenStream {
    let mut construction_statements = Vec::new();
    // construction_statements.push(quote! { let mut #vec_builder_ident = Vec::new(); });

    for item in items {
        match item {
            ArgItem::Regular(smt) => {
                let smt_code = generate_code(smt); // generate_code returns code for one SmtFormula
                construction_statements.push(quote! { [#smt_code] });
            }
            ArgItem::SplatExpr(expr_to_splat) => {
                // Assume expr_to_splat evaluates to an iterable of items convertible to SmtFormula
                construction_statements
                    .push(quote! { (#expr_to_splat).into_iter().map(|item| item.into()) });
            }
            ArgItem::SplatIdent(ident_to_splat) => {
                // Assume ident_to_splat is an iterable of items convertible to SmtFormula
                construction_statements
                    .push(quote! { (#ident_to_splat).into_iter().map(|item| item.into()) });
            }
        }
    }

    quote! {
        {
            ::itertools::chain![#(#construction_statements),*].collect()
        }
    }
}

fn generate_code(Ast { inner: parsed, .. }: Ast) -> proc_macro2::TokenStream {
    let crate_path = quote! { ::cryptovampire_smt };

    match parsed {
        InnerAst::True => quote! { #crate_path::SmtFormula::True },
        InnerAst::False => quote! { #crate_path::SmtFormula::False },
        InnerAst::Banged(banged_content) => {
            let tokens = generate_banged_expr_tokens(banged_content);
            quote! { (#tokens).into() }
        }
        InnerAst::And(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::And(#processed_args) }
        }
        InnerAst::Or(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Or(#processed_args) }
        }
        InnerAst::Eq(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Eq(#processed_args) }
        }
        InnerAst::Neq(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Neq(#processed_args) }
        }
        InnerAst::Not(arg) => {
            let processed_arg = generate_code(*arg);
            quote! { #crate_path::SmtFormula::Not(Box::new(#processed_arg)) }
        }
        InnerAst::Implies(a, b) => {
            let [a, b] = [*a, *b].map(generate_code);
            quote! {#crate_path::SmtFormula::Implies(Box::new(#a), Box::new(#b))}
        }
        InnerAst::FunApp { func, args } => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
                                                      // As per your change, #func (the Ident) is passed directly.
                                                      // This implies SmtFormula::Fun can handle an Ident or its type N in
                                                      // SmtFormula<N,S> can be From<Ident> or similar.
            quote! { #crate_path::SmtFormula::Fun(#func.clone(), #processed_args) }
        }
        InnerAst::Quantifier {
            kind,
            bindings,
            body,
        } => {
            // Determine if it's Forall or Exists for the final constructor
            let constructor = match kind {
                QuantifierKind::Forall => quote! { #crate_path::SmtFormula::Forall },
                QuantifierKind::Exists => quote! { #crate_path::SmtFormula::Exists },
            };
            let processed_body = generate_code(*body);

            match bindings {
                VarBindings::Binding(bindings) => {
                    generate_quant_with_binders(crate_path, constructor, processed_body, bindings)
                }
                VarBindings::Expr(expr) => quote! {#constructor(#expr, Box::new(#processed_body))},
                VarBindings::Ident(ident) => {
                    quote! {#constructor(#ident, Box::new(#processed_body))}
                }
            }
        }
    }
}

fn generate_quant_with_binders(
    crate_path: proc_macro2::TokenStream,
    constructor: proc_macro2::TokenStream,
    processed_body: proc_macro2::TokenStream,
    bindings: Vec<VarBinding>,
) -> proc_macro2::TokenStream {
    // Generate `let __smt_idx_temp_N = index_expr; let user_var = SmtFormula::Var(__smt_idx_temp_N);`
    // And collect the __smt_idx_temp_N idents.
    let mut let_bindings = Vec::new();
    let mut temp_var_idents_for_sorted_var = Vec::new();

    for binding in bindings.iter() {
        let user_var_name = &binding.name;
        let index_eval_expr = generate_var_index_expr_tokens(&binding.index);

        let i = VAR_COUNTER.fetch_add(1, Ordering::AcqRel);
        // Create a hygienically distinct temporary variable name for the evaluated index
        let temp_index_var_ident = format_ident!(
            "__smt_idx_temp_{}",
            i,
            span = proc_macro2::Span::call_site()
        );

        match user_var_name {
            VarName::Underscore(_) => let_bindings.push(quote! {
                let #temp_index_var_ident = #crate_path::VarInner::Int(#index_eval_expr);
            }),
            VarName::Ident(user_var_name) => let_bindings.push(quote! {
                let #temp_index_var_ident = #crate_path::VarInner::Int(#index_eval_expr);
                let #user_var_name = #crate_path::SmtFormula::Var(#temp_index_var_ident.clone());
            }),
        }

        temp_var_idents_for_sorted_var.push(temp_index_var_ident);
    }

    let sorted_vars_elements: Vec<_> = bindings
        .iter()
        .zip(temp_var_idents_for_sorted_var.iter())
        .map(|(binding, temp_idx_ident)| {
            let sort_expr = &binding.sort;
            quote! { #crate_path::SortedVar { var: #temp_idx_ident, sort: #sort_expr } }
        })
        .collect();

    quote! {
        {
            #(#let_bindings)*
            #constructor( // Use the Forall or Exists constructor
                vec![ #(#sorted_vars_elements),* ],
                Box::new(#processed_body)
            )
        }
    }
}

pub fn smt_formulas(input: TokenStream) -> TokenStream {
    let parsed_smt = parse_macro_input!(input as Ast);
    generate_code(parsed_smt).into()
}

pub fn smt_many_smt_formulas(input: TokenStream) -> TokenStream {
    let parser = Punctuated::<Ast, Token![,]>::parse_terminated;
    let codes = parser.parse(input).unwrap().into_iter().map(generate_code);

    quote! {
        vec![#(#codes),*]
    }
    .into()
}
