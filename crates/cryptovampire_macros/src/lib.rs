use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use syn::{
    parse_macro_input, spanned::Spanned, DataEnum, DataStruct, DeriveInput, GenericParam, Lifetime,
    LifetimeParam, PredicateType, WherePredicate,
};

#[proc_macro_derive(LocationProvider, attributes(provider))]
pub fn with_location_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let data = match &input.data {
    syn::Data::Struct(data_struct) => data_struct,
    _ => return quote_spanned! {input.span() => compile_error!("only struct are supported, please implement by hand");}.into()
  };

    let mut iter = data.fields.iter().filter(|f| {
        f.attrs
            .iter()
            .filter(|attr| attr.path().is_ident("provider"))
            .next()
            .is_some()
    });

    let field = if let Some(field) = iter.next() {
        field
    } else {
        return quote_spanned! {input.span() => compile_error!("no attribute 'provider'");}.into();
    };

    if let Some(f) = iter.next() {
        return quote_spanned! {
          f.ident.span() =>
            compile_error!("only on 'provider' is allowed");
        }
        .into();
    }
    let field_ty = &field.ty;
    let field_iden = &field.ident;

    let mut gen_clone = input.generics.clone();

    // gen_clone.type_params_mut().for_each(|tp| {
    //   let mut tmp = Vec::with_capacity(tp.attrs.len());
    //   while let Some(attr) = tp.attrs.pop() {
    //     if !attr.path().is_ident("disp") {
    //       tmp.push(attr);
    //     }
    //   }
    //   tp.attrs = tmp;
    // });

    let lt = Lifetime::new("'a____secret", Span::call_site());
    let ltp = LifetimeParam::new(lt.clone());
    gen_clone.params.push(GenericParam::from(ltp));
    // let mut where_clause = gen_clone.make_where_clause();

    let (impl_generics, _, _) = gen_clone.split_for_impl();
    let (_, ty_generics, where_clause) = input.generics.split_for_impl();

    // let disp_ty = input
    //     .generics
    //     .type_params()
    //     .filter(|t| {
    //         t.attrs
    //             .iter()
    //             .filter(|attr| attr.path().is_ident("disp"))
    //             .next()
    //             .is_some()
    //     })
    //     .map(|t| &t.ident);

    let where_clause = {
        let w = where_clause.map(|w| &w.predicates);
        quote! {
          where
            #field_ty : crate::error::PreLocation,
            // #(#disp_ty: std::fmt::Display,)*
            S: std::fmt::Display,
            #w
        }
    };

    let l_ty = quote! {<#field_ty as crate::error::PreLocation>::L};

    quote! {
      impl #impl_generics crate::error::LocationProvider<#l_ty> for & #lt #name #ty_generics #where_clause {
        fn provide(self) -> #l_ty {
          use crate::error::PreLocation;
          self.#field_iden.help_provide(self)
        }
      }
    }.into()
}
