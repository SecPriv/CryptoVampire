use proc_macro::TokenStream;
use quote::quote;
use quote::quote_spanned;
use syn::parenthesized;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned,
    DeriveInput, Expr, Token,
};

#[proc_macro_derive(LocationProvider, attributes(provider))]
pub fn with_location_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    match &input.data {
        syn::Data::Struct(data) => with_location::derive_struct(data, &input),
        syn::Data::Enum(data) => with_location::derive_enum(data, &input),
        _ => quote_spanned! {input.span() => compile_error!("no unions");}.into(),
    }
}

mod with_location;

#[proc_macro]
pub fn mk_builtin_funs(input: TokenStream) -> TokenStream {
    indistinguishability::mk_builtin_funs(input)
}

mod indistinguishability;

mod smt;
#[proc_macro]
pub fn smt_formula(input: TokenStream) -> TokenStream {
    smt::smt_formulas(input)
}

// #[derive(Debug)]
// struct SExpr(String);

// struct Rule {
//     head: ,
//     body: Option<Punctuated<SExpr, Token![,]>>,
//     cut: bool
// }

// impl Parse for SExpr {
//     fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
//         let content;

//         let tokens = parenthesized!(content in input);
//         Ok(SExpr(format!("({})", tokens.to_string())))
//     }
// }

// struct PrologRulesInput {
//     rules: Vec<Rule>,
// }

// impl Parse for Rule {
//     fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
//         let head: Expr = input.parse()?;

//         if input.peek(Token![:]) {
//             let _: Token![:] = input.parse()?;
//             let _: Token![-] = input.parse()?;
//             let cut: Option<Token![!]> = input.parse()?;
//             let body = Punctuated::parse_terminated(input)?;
//             Ok(Rule {
//                 head,
//                 body: Some(body),
//                 cut : cut.is_some()
//             })
//         } else {
//             Ok(Rule { head, body: None, cut:false })
//         }
//     }
// }

// impl Parse for PrologRulesInput {
//     fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
//         let mut rules = Vec::new();
//         while !input.is_empty() {
//             let rule: Rule = input.parse()?;
//             let _: Token![.] = input.parse()?; // consume `.`
//             rules.push(rule);
//         }
//         Ok(PrologRulesInput { rules })
//     }
// }

// #[proc_macro]
// pub fn prolog_rules(input: TokenStream) -> TokenStream {
//     let PrologRulesInput { rules } = parse_macro_input!(input as PrologRulesInput);

//     let rule_exprs = rules.into_iter().map(|Rule { head, body, cut }| {
//         let head_str = quote!(#head).to_string();
//         let cut = if cut {quote! {true}} else {quote! {false}};

//         match body {
//             Some(body_exprs) => {
//                 let body_strs = body_exprs.iter().map(|e| quote!(#e).to_string());
//                 quote! {
//                     indistinguishability::rule::PrologRule {
//                         input: #head_str.parse().unwrap(),
//                         deps: [#(#body_strs),*].into_iter().map(|s| s.parse().unwrap()).collect(),
//                         cut: #cut
//                     }
//                 }
//             }
//             None => {
//                 quote! {
//                     indistinguishability::rule::PrologRule {
//                         input: #head_str.parse().unwrap(),
//                         deps: vec![]
//                         cut: #cut
//                     }
//                 }
//             }
//         }
//     });

//     let output = quote! {
//         vec![ #(#rule_exprs),* ]
//     };

//     output.into()
// }
