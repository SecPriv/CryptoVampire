use itertools::{Itertools, chain};
use proc_macro::TokenStream;
use quote::{quote, quote_spanned};
use syn::parse::{Parse, ParseStream};
use syn::{
    Attribute, FieldValue, Ident, LitStr, Member, Token, braced, parse_macro_input, parse_quote,
};

/// represents things like
///
/// ```text
/// NOT "bit_not" "not" "mnot" {
///    signature: s!(Bool, 1),
///    flags: f!(/* ALIAS | */ BUILTIN_SMT),
///    alias: Some(alias!{
///        0:Bool in rexp!(#0) => rexp!((BITE #0 FALSE TRUE))
///    }),
/// };
/// ```
///
/// This will generate a new function with the given name and fields.
/// The fields are merged with the ones declared at the to of the macro call
#[derive(Clone)]
struct MFunction {
    /// The name of the function.
    name: Ident,
    /// The span of the function definition.
    span: proc_macro2::Span,
    /// Alternative names for the function.
    alt_names: Vec<LitStr>,
    /// The fields of the function.
    fields: Vec<FieldValue>,
    /// Attributes applied to the function.
    attrs: Vec<Attribute>,
}

impl Parse for MFunction {
    /// Parses an `MFunction` from the input token stream.
    fn parse(input: ParseStream<'_>) -> syn::Result<Self> {
        let span = input.span();
        let attrs = input.call(Attribute::parse_outer)?;
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
            attrs,
        })
    }
}

/// Represents the input to the `mk_builtin_funs` macro.
struct Input {
    /// Default field values for functions.
    default: Vec<FieldValue>,
    /// Function declarations.
    decls: Vec<MFunction>,
}

impl Parse for Input {
    /// Parses an `Input` from the input token stream.
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
    /// Merges the function with other field values, prioritizing existing fields.
    pub fn merge(mut self, other: &[FieldValue]) -> Self {
        let to_add: Vec<&FieldValue> = other
            .iter()
            .filter(|f| !self.members().contains(&f.member))
            .collect();
        self.fields.extend(to_add.into_iter().cloned());
        self
    }

    /// Returns an iterator over the members of the function's fields.
    fn members(&self) -> impl Iterator<Item = &Member> {
        self.fields.iter().map(|f| &f.member)
    }

    /// Generates the token stream for declaring the function.
    pub fn declare(&self) -> proc_macro2::TokenStream {
        let fields: proc_macro2::TokenStream = self.fields.iter().map(|f| quote! {#f ,}).collect();
        let name = &self.name;
        let attrs = &self.attrs;
        quote_spanned! { self.span =>
            #(#attrs)*
            pub static #name: Function = {
                static TMP : InnerSmartCow<InnerFunction> = InnerSmartCow::mk_static(InnerFunction {#fields});
                Function::from_ref(&TMP)
            };
        }
    }

    /// Returns the token stream for an owned version of the function.
    pub fn as_owned(&self) -> proc_macro2::TokenStream {
        let name = &self.name;
        // let span = self.span;

        quote_spanned! {self.span => #name.const_clone()}
    }

    /// Returns an iterator over the alternative names and their corresponding owned function token streams.
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
