use proc_macro::TokenStream;
use quote::quote_spanned;
use syn::spanned::Spanned;
use syn::{DeriveInput, parse_macro_input};

/// Derives the `LocationProvider` trait for structs and enums.
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

mod indistinguishability;
/// Generates builtin functions for indistinguishability proofs.
#[proc_macro]
pub fn mk_builtin_funs(input: TokenStream) -> TokenStream {
    indistinguishability::mk_builtin_funs(input)
}

mod formulas;
/// Generates SMT formulas from a given input.
#[proc_macro]
pub fn smt(input: TokenStream) -> TokenStream {
    formulas::smt_formulas(input)
}

/// Generates multiple SMT formulas from a given input.
#[proc_macro]
pub fn vec_smt(input: TokenStream) -> TokenStream {
    formulas::smt_many_smt_formulas(input)
}

/// Generates multiple SMT formulas with comments from a given input.
#[proc_macro]
pub fn vec_smt2(input: TokenStream) -> TokenStream {
    formulas::smt_many_smt_with_comments(input)
}

/// Generates a `RecExpr` from a given input.
#[proc_macro]
pub fn recexpr(input: TokenStream) -> TokenStream {
    formulas::mk_recexpr(input)
}
// #[proc_macro]
// pub fn declare_recexpr(input: TokenStream) -> TokenStream {
//     formulas::declare_static_recexpr(input)
// }
