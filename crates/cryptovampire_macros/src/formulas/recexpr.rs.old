use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::default;

use itertools::Itertools;
use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::parse::Parse;
use syn::{Error, Ident, LitInt, PathSegment, Token, parse_macro_input, parse_quote};
use utils::implvec;

use crate::formulas::parser::{ArgItem, Ast, BangedContent, FunIdent, InnerAst};

fn fold(
    path: &syn::Path,
    span: Span,
    func: PathSegment,
    args: Vec<ArgItem>,
    default: Option<PseudoTree>,
    simp_two: bool,
) -> syn::Result<PseudoTree> {
    let mut args: Vec<_> = args
        .into_iter()
        .map(|x| transform_arg_item(path, x))
        .try_collect()?;

    let Some(a) = args.pop() else {
        return default.ok_or(Error::new(span, "no arguments"));
    };
    let Some(b) = args.pop() else {
        return simp_two
            .then_some(a)
            .ok_or(Error::new(span, "only 1 argument (needs at least 2)"));
    };

    let func: FunIdent = mk_path(path, func).into();
    let init = PseudoTree::App(func.clone(), vec![a, b]);
    let res = args
        .into_iter()
        .fold(init, |acc, x| PseudoTree::App(func.clone(), vec![acc, x]));

    Ok(res)
}

fn transform_arg_item(path: &syn::Path, arg: ArgItem) -> syn::Result<PseudoTree> {
    match arg {
        ArgItem::Regular(ast) => Ok(PseudoTree::new(path, ast)?),
        ArgItem::SplatExpr(expr) => Err(Error::new_spanned(expr, "no `*` expressions")),
        ArgItem::SplatIdent(ident) => Err(Error::new_spanned(ident, "no `*` expressions")),
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum PseudoTree {
    App(FunIdent, Vec<PseudoTree>),
    Var(BangedContent),
}

fn mk_app(path: &syn::Path, ident: &FunIdent, args: implvec!(usize)) -> TokenStream {
    let args = args.into_iter().map(|x| x as u32);
    quote! {
      #path::mk_app(&#ident, [#(#args),*])
    }
}

fn mk_var(path: &syn::Path, lit: &BangedContent) -> TokenStream {
    match lit {
        BangedContent::Lit(syn::Lit::Int(lit)) => quote! {
          #path::mk_var(#lit)
        },
        BangedContent::Ident(ident) => quote! {#ident.clone() },
        BangedContent::Expr(expr) => quote! { #expr },
        _ => panic!("litteral need to be number for variables"),
    }
}

fn mk_path(path: &syn::Path, segment: PathSegment) -> syn::Path {
    let mut path = path.clone();
    path.segments.push(segment);
    path
}

impl PseudoTree {
    pub fn mk_true(path: &syn::Path) -> Self {
        Self::App(mk_path(path, parse_quote!(TRUE)).into(), vec![])
    }
    pub fn mk_false(path: &syn::Path) -> Self {
        Self::App(mk_path(path, parse_quote!(FALSE)).into(), vec![])
    }

    pub fn new(path: &syn::Path, Ast { span, inner }: Ast) -> syn::Result<Self> {
        use InnerAst::*;
        match inner {
            And(args) => fold(
                path,
                span,
                parse_quote!(AND),
                args,
                Some(Self::mk_true(path)),
                true,
            ),
            Or(args) => fold(
                path,
                span,
                parse_quote!(OR),
                args,
                Some(Self::mk_false(path)),
                true,
            ),
            Eq(args) => fold(path, span, parse_quote!(EQ), args, None, false),
            Neq(args) => Ok(Self::App(
                mk_path(path, parse_quote!(NOT)).into(),
                vec![fold(path, span, parse_quote!(EQ), args, None, false)?],
            )),
            Not(arg) => Ok(Self::App(
                mk_path(path, parse_quote!(NOT)).into(),
                vec![Self::new(path, *arg)?],
            )),
            Implies(a, b) => Ok(Self::App(
                mk_path(path, parse_quote!(IMPLIES)).into(),
                vec![Self::new(path, *a)?, Self::new(path, *b)?],
            )),
            FunApp { func, args } => Ok(Self::App(
                func,
                args.into_iter()
                    .map(|x| transform_arg_item(path, x))
                    .try_collect()?,
            )),
            True => Ok(Self::mk_true(path)),
            False => Ok(Self::mk_false(path)),
            Quantifier { .. } => Err(syn::Error::new(span, "no quantifier allowed")),
            Banged(b) => Ok(Self::Var(b)),
        }
    }

    pub fn extend_rec_expr<'a>(
        &'a self,
        path: &syn::Path,
        expr: &mut Vec<TokenStream>,
        seen: &mut HashMap<&'a Self, usize>,
    ) -> usize {
        if let Some(n) = seen.get(self) {
            return *n;
        }

        let ts = match self {
            PseudoTree::Var(lit) => mk_var(path, lit),
            PseudoTree::App(ident, args) => {
                let args = args.iter().map(|pt| pt.extend_rec_expr(path, expr, seen));
                mk_app(path, ident, args)
            }
        };
        expr.push(ts);

        let n = expr.len() - 1;
        seen.insert(self, n);
        n
    }

    pub fn count(&self) -> usize {
        match self {
            PseudoTree::App(_, args) => 1 + args.iter().map(Self::count).sum::<usize>(),
            PseudoTree::Var(_) => 1,
        }
    }
}

struct MkRecExpr {
    path: syn::Path,
    ast: Ast,
}

impl Parse for MkRecExpr {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let path = input.parse()?;
        let _: Token![;] = input.parse()?;
        let ast = input.parse()?;
        Ok(Self { path, ast })
    }
}

pub fn mk_const_recexpr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let MkRecExpr { path, ast } = parse_macro_input!(input as MkRecExpr);
    let tree = PseudoTree::new(&path, ast).unwrap();
    let n = tree.count();
    let mut expr = Vec::with_capacity(n);
    let mut seen = HashMap::with_capacity(n);
    tree.extend_rec_expr(&path, &mut expr, &mut seen);
    quote! { [#(#expr),*] }.into()
}

struct MkRecExprStatic {
    name: Ident,
    path: syn::Path,
    ast: Ast,
}

impl Parse for MkRecExprStatic {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let path = input.parse()?;
        let _: Token![in] = input.parse()?;
        let name = input.parse()?;
        let _: Token![=] = input.parse()?;
        let ast = input.parse()?;
        Ok(Self { name, path, ast })
    }
}

pub fn declare_static_recexpr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let MkRecExprStatic { name, path, ast } = parse_macro_input!(input as MkRecExprStatic);
    let tree = PseudoTree::new(&path, ast).unwrap();
    let n = tree.count();
    let mut expr = Vec::with_capacity(n);
    let mut seen = HashMap::with_capacity(n);
    tree.extend_rec_expr(&path, &mut expr, &mut seen);
    let n = expr.len();
    quote! {static #name : [#path::RexpLang; #n] = [#(#expr),*]; }.into()
}
