// In your proc-macro crate's src/lib.rs

use std::sync::atomic::AtomicUsize;

use proc_macro::TokenStream;
use quote::{quote, quote_spanned}; // format_ident is key here
use syn::parse::{Parse, ParseStream, Parser, Result};
use syn::punctuated::Punctuated;
use syn::{Token, parse_macro_input};

// Counter for generating unique temporary variable names
static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);

use super::parser::*;

struct MacroInput<C = ()> {
    path: syn::Path,
    content: C,
}

impl<C> MacroInput<C> {
    fn path(&self) -> &syn::Path {
        &self.path
    }
}

impl<C: Parse> Parse for MacroInput<C> {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let path = input.parse()?;
        input.parse::<Token![;]>()?;
        let content = input.parse()?;
        Ok(Self { path, content })
    }
}

fn generate_banged_expr_tokens(
    mi: &MacroInput,
    BangedContent { kind, inner }: BangedContent,
) -> proc_macro2::TokenStream {
    let ret = match inner {
        BangedContentInner::Ident(ident) => quote! { #ident.clone() },
        BangedContentInner::Expr(expr) => quote! { (#expr) }, // Parenthesize expr just in case
    };
    match kind {
        BangedContentKind::ExplamationMark(_) => {
            let path = mi.path();
            quote!(#path::SmtFormula::Var(#ret))
        }
        BangedContentKind::Cross(_) => ret,
    }
}

fn generate_var_index_expr_tokens(mi: &MacroInput, v_idx: &VarIndex) -> proc_macro2::TokenStream {
    match v_idx {
        // VarIndex::Lit(lit_int) => quote! { #lit_int },
        VarIndex::Expr(expr) => quote! { (#expr) }, // Parenthesize expr
        VarIndex::Ident(ident) => quote! { #ident.clone() },
    }
}

fn generate_args(mi: &MacroInput, items: ArgsVec) -> proc_macro2::TokenStream {
    let mut construction_statements = Vec::new();
    // construction_statements.push(quote! { let mut #vec_builder_ident = Vec::new(); });

    for item in items {
        match item {
            ArgItem::Regular(smt) => {
                let smt_code = generate_code(mi, smt); // generate_code returns code for one SmtFormula
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

fn generate_code(mi: &MacroInput, Ast { inner: parsed, .. }: Ast) -> proc_macro2::TokenStream {
    let crate_path = mi.path();

    match parsed {
        InnerAst::True => quote! { #crate_path::SmtFormula::True },
        InnerAst::False => quote! { #crate_path::SmtFormula::False },
        InnerAst::Banged(banged_content) => {
            let tokens = generate_banged_expr_tokens(mi, banged_content);
            quote! { (#tokens).into() }
        }
        InnerAst::And(args) => {
            let processed_args = generate_args(mi, args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::And(#processed_args) }
        }
        InnerAst::Or(args) => {
            let processed_args = generate_args(mi, args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Or(#processed_args) }
        }
        InnerAst::Eq(args) => {
            let processed_args = generate_args(mi, args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Eq(#processed_args) }
        }
        InnerAst::Neq(args) => {
            let processed_args = generate_args(mi, args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Neq(#processed_args) }
        }
        InnerAst::Not(arg) => {
            let processed_arg = generate_code(mi, *arg);
            quote! { #crate_path::SmtFormula::Not(Box::new(#processed_arg)) }
        }
        InnerAst::Implies(a, b) => {
            let [a, b] = [*a, *b].map(|x| generate_code(mi, x));
            quote! {#crate_path::SmtFormula::Implies(Box::new(#a), Box::new(#b))}
        }
        InnerAst::FunApp(FunAppAst { func, args }) => {
            let processed_args = generate_args(mi, args); //args.into_iter().map(generate_code);
            // As per your change, #func (the Ident) is passed directly.
            // This implies SmtFormula::Fun can handle an Ident or its type N in
            // SmtFormula<N,S> can be From<Ident> or similar.
            quote! { #crate_path::SmtFormula::Fun(#func.clone(), #processed_args) }
        }
        InnerAst::Quantifier(QuantifierAst {
            kind,
            bindings,
            body,
        }) => {
            // Determine if it's Forall or Exists for the final constructor
            let constructor = match kind {
                QuantifierKind::Forall(_) => {
                    quote_spanned! {kind.span() =>  #crate_path::SmtFormula::Forall }
                }
                QuantifierKind::Exists(_) => {
                    quote_spanned! {kind.span() =>  #crate_path::SmtFormula::Exists }
                }
                QuantifierKind::FindSuchThat(_) => {
                    quote_spanned! {kind.span() => ::std::compile_error!("'find such that' doesn't exists in smt")}
                }
            };
            let body = match body.into_iter().next() {
                Some(ArgItem::Regular(ast)) => ast,
                _ => return quote! {::std::compile_error!("wrong arguments to quantifier")},
            };
            let processed_body = generate_code(mi, body);

            match bindings {
                VarBindings::Binding(bindings) => {
                    generate_quant_with_binders(mi, constructor, processed_body, bindings)
                }
                VarBindings::Expr(expr) => {
                    quote! {#constructor({ #expr }.into_iter().collect(), Box::new(#processed_body))}
                }
                VarBindings::Ident(ident) => {
                    quote! {#constructor(#ident.into_iter().collect(), Box::new(#processed_body))}
                }
            }
        }
    }
}

fn generate_quant_with_binders(
    mi: &MacroInput,
    // crate_path: proc_macro2::TokenStream,
    constructor: proc_macro2::TokenStream,
    processed_body: proc_macro2::TokenStream,
    bindings: Vec<VarBinding>,
) -> proc_macro2::TokenStream {
    let path = mi.path();
    let (let_bindings, names): (Vec<_>, Vec<_>) = bindings
        .iter()
        .map(|VarBinding { name, sort }| (quote!(let #name = #path::fresh!(#sort);), name))
        .unzip();

    quote! {
        {
            #(#let_bindings)*
            #constructor( // Use the Forall or Exists constructor
                vec![ #(#names.clone()),* ],
                Box::new(#processed_body)
            )
        }
    }
}

pub fn smt_formulas(input: TokenStream) -> TokenStream {
    let MacroInput { path, content } = parse_macro_input!(input as MacroInput<Ast>);
    let mi = MacroInput { path, content: () };
    generate_code(&mi, content).into()
}

impl<C: Parse> MacroInput<Vec<C>> {
    fn parse_alt(input: ParseStream<'_>) -> Result<Self> {
        let path = input.parse()?;
        input.parse::<Token![;]>()?;
        let parser = Punctuated::<C, Token![,]>::parse_terminated(input)?;
        Ok(Self {
            path,
            content: parser.into_iter().collect(),
        })
    }
}

pub fn smt_many_smt_formulas(input: TokenStream) -> TokenStream {
    let MacroInput { path, content } = parse_macro_input!(input with MacroInput::parse_alt);
    let mi = MacroInput { path, content: () };
    let codes = content.into_iter().map(|x| generate_code(&mi, x));

    quote! {
        vec![#(#codes),*]
    }
    .into()
}

enum SmtWithComments {
    Comment(syn::Expr),
    Ast(Ast),
}

impl Parse for SmtWithComments {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![;]) {
            let _: Token![;] = input.parse()?;
            Ok(Self::Comment(input.parse()?))
        } else {
            Ok(Self::Ast(input.parse()?))
        }
    }
}

pub fn smt_many_smt_with_comments(input: TokenStream) -> TokenStream {
    let MacroInput { path, content } = parse_macro_input!(input with MacroInput::parse_alt);
    let mi = MacroInput {
        path: path.clone(),
        content: (),
    };
    let codes = content.into_iter().map(|x| match x {
        SmtWithComments::Comment(e) => quote!(#path::Smt::Comment(#e)),
        SmtWithComments::Ast(ast) => {
            let expr = generate_code(&mi, ast);
            quote!(#path::Smt::mk_assert(#expr))
        }
    });

    quote! {
        vec![#(#codes),*]
    }
    .into()
}
