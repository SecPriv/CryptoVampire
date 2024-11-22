use proc_macro::TokenStream;
use quote::quote_spanned;
use syn::{
    parse_macro_input, spanned::Spanned, DeriveInput
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
