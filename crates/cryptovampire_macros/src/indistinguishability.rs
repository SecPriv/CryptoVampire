use std::collections::HashMap;

use itertools::{Itertools, chain};
use proc_macro::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{
    Expr, FieldValue, Ident, LitStr, Member, Token, braced,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    token::{Brace, Impl},
};

#[derive(Clone)]
struct MFunction {
    name: Ident,
    span: proc_macro2::Span,
    alt_names: Vec<LitStr>,
    fields: Vec<FieldValue>,
}

struct Input {
    default: Vec<FieldValue>,
    decls: Vec<MFunction>,
}

impl Parse for MFunction {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let span = input.span();
        let name: Ident = input.parse()?;

        let mut alt_names = vec![];
        while !input.is_empty() && input.peek(LitStr) {
            alt_names.push(input.parse()?);
        }
        let str_name = alt_names.first().unwrap();

        let content;
        let _ = braced!(content in input);
        let mut fields: Vec<_> = content
            .parse_terminated(FieldValue::parse, Token![,])?
            .into_iter()
            .collect();
        fields.push(parse_quote!(name: Cow::Borrowed(#str_name)));
        Ok(MFunction {
            name,
            span,
            alt_names,
            fields,
        })
    }
}

impl Parse for Input {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let default = {
            let content;
            let _ = braced!(content in input);
            content
                .parse_terminated(FieldValue::parse, Token![,])?
                .into_iter()
                .collect()
        };
        let _: Token![;] = input.parse()?;

        let funs = input.parse_terminated(MFunction::parse, Token![;])?;
        Ok(Self {
            default,
            decls: funs.into_iter().collect(),
        })
    }
}

impl MFunction {
    pub fn merge(mut self, other: &[FieldValue]) -> Self {
        let to_add: Vec<&FieldValue> = other
            .iter()
            .filter(|f| !self.members().contains(&f.member))
            .collect();
        self.fields.extend(to_add.into_iter().cloned());
        self
    }

    fn members(&self) -> impl Iterator<Item = &Member> {
        self.fields.iter().map(|f| &f.member)
    }

    pub fn declare(&self) -> proc_macro2::TokenStream {
        let fields: proc_macro2::TokenStream = self.fields.iter().map(|f| quote! {#f ,}).collect();
        let name = &self.name;
        quote_spanned! { self.span =>
            pub static #name: Function = Function::from_ref(&InnerFunction {#fields});
        }
    }

    pub fn as_owned(&self) -> proc_macro2::TokenStream {
        let name = &self.name;
        // let span = self.span;

        quote_spanned! {self.span => #name.const_clone().unwrap()}
    }

    pub fn list_alt_names(&self) -> impl Iterator<Item = proc_macro2::TokenStream> + use<'_> {
        let owned = self.as_owned();
        let name = &self.name;
        chain![
            // [quote_spanned! {self.span => (#name, #owned)}],
            self.alt_names.iter().map(move |n| quote! {(#n, #owned)})
        ]
    }
}

pub fn mk_builtin_funs(input: TokenStream) -> TokenStream {
    let Input { default, decls } = parse_macro_input!(input as Input);
    let decls: Vec<_> = decls.into_iter().map(|f| f.merge(&default)).collect();

    let defines = decls.iter().map(MFunction::declare);
    let names = decls.iter().map(|f| f.as_owned());
    let alt_names = decls.iter().flat_map(|f| f.list_alt_names());

    quote! {
        #(#defines)*
        pub static BUILTINS : &[Function] = &[#(#names),*];
        pub static PARSING_PAIRS: &[(&str, Function)] = &[#(#alt_names),*];
    }
    .into()
}
