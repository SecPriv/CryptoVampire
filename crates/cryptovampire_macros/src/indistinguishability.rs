use std::collections::HashMap;

use itertools::Itertools;
use proc_macro::TokenStream;
use quote::quote;
use syn::{
    braced,
    parse::{Parse, ParseStream},
    parse_macro_input, parse_quote,
    punctuated::Punctuated,
    Expr, FieldValue, Ident, Member, Token,
};

#[derive(Clone)]
struct MFunction {
    name: Ident,
    fields: Vec<FieldValue>,
}

struct Input {
    default: Vec<FieldValue>,
    decls: Vec<MFunction>,
}

impl Parse for MFunction {
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let name: Ident = input.parse()?;
        let content;
        let _ = braced!(content in input);
        let fields = content.parse_terminated(FieldValue::parse, Token![,])?;
        Ok(MFunction {
            name,
            fields: fields.into_iter().collect(),
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
        let fields: proc_macro2::TokenStream =
            self.fields.iter().map(|f| quote! {#f ,}).collect();
        let name = &self.name;
        quote! {
            pub static #name: Function = Function::from_ref(&InnerFunction {#fields});
        }
    }
}

pub fn mk_builtin_funs(input: TokenStream) -> TokenStream {
    let Input { default, decls } = parse_macro_input!(input as Input);
    let decls: Vec<_> = decls.into_iter().map(|f| f.merge(&default)).collect();

    let defines = decls.iter().map(MFunction::declare);
    let array = {
        let names = decls.iter().map(|f| &f.name);
        quote! { &[#(&#names),*] }
    };

    quote! {
        #(#defines)*
        pub static BUILTINS_TO_DECLARE : &[&Function] = #array;
    }
    .into()
}
