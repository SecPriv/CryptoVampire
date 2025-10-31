use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{
    DataEnum, DataStruct, DeriveInput, Field, Fields, GenericParam, Lifetime, LifetimeParam,
};

fn find_field(span: Span, fields: &Fields) -> Result<(usize, &Field), proc_macro2::TokenStream> {
    let mut iter = fields
        .iter()
        .enumerate()
        .filter(|(_, f)| f.attrs.iter().any(|attr| attr.path().is_ident("provider")));

    let field = if let Some(field) = iter.next() {
        field
    } else {
        return Err(quote_spanned! {span => compile_error!("no attribute 'provider'");});
    };

    if let Some(f) = iter.next() {
        return Err(quote_spanned! {
          f.1.ident.span() =>
            compile_error!("only one 'provider' is allowed");
        });
    }
    Ok(field)
}

fn finalize(
    input: &DeriveInput,
    // f_ty: &Type,
    implementation: proc_macro2::TokenStream,
) -> TokenStream {
    let name = &input.ident;
    let mut gen_clone = input.generics.clone();
    let lt = Lifetime::new("'a____secret", Span::call_site());
    let ltp = LifetimeParam::new(lt.clone());
    gen_clone.params.push(GenericParam::from(ltp));
    // let mut where_clause = gen_clone.make_where_clause();

    let (impl_generics, _, _) = gen_clone.split_for_impl();
    let (_, ty_generics, where_clause) = input.generics.split_for_impl();

    let where_clause = {
        let w = where_clause.map(|w| &w.predicates);
        quote! {
          where
            // #f_ty : crate::error::PreLocation,
            S: std::fmt::Display + std::fmt::Debug,
            #w
        }
    };

    // let l_ty = quote! {<#f_ty as crate::error::PreLocation>::L};

    quote! {
      impl #impl_generics crate::error::LocationProvider for & #lt #name #ty_generics #where_clause {
        fn provide(self) -> crate::error::Location {
          #implementation
        }
      }
    }.into()
}

/// Derives the `LocationProvider` trait for a struct.
pub fn derive_struct(data: &DataStruct, input: &DeriveInput) -> TokenStream {
    let (i, field) = match find_field(input.span(), &data.fields) {
        Ok(x) => x,
        Err(x) => return x.into(),
    };

    // let f_ty = &field.ty;
    let field_iden = match &field.ident {
        Some(x) => quote! {#x},
        None => quote! {#i},
    };
    let implementation = quote! {
      use crate::error::LocateHelper;
      self.#field_iden.help_provide(&self)
    };

    finalize(input, /* f_ty, */ implementation)
}

/// Derives the `LocationProvider` trait for an enum.
pub fn derive_enum(data: &DataEnum, input: &DeriveInput) -> TokenStream {
    let name = &input.ident;
    // let f_ty = &match data
    //     .variants
    //     .iter()
    //     .next()
    //     .map(|v| find_field(input.span(), &v.fields))
    // {
    //     Some(Ok(f)) => f,
    //     Some(Err(x)) => return x.into(),
    //     None => return quote_spanned! {input.span() => compile_error!("empty enum!");}.into(),
    // }
    // .1.ty;

    let implementations = data.variants.iter().map(|v| {
        let iden = &v.ident;
        match find_field(v.span(), &v.fields) {
            Ok((i, field)) => {
                let field_iden = match &field.ident {
                    Some(x) => quote! {#x},
                    None => quote! {#i},
                };
                quote! {#name::#iden {#field_iden: x, ..} => {
                  use crate::error::LocateHelper;
                  x.help_provide(&self)
                }}
            }
            Err(err) => {
                quote! {
                  #name::#iden {..} => {
                    #err
                  }
                }
            }
        }
    });
    let implementation = quote! {
      match self {
        #(#implementations)*
      }
    };
    finalize(input, /* f_ty, */ implementation)
}
