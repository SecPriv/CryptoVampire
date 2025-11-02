use itertools::{Itertools, izip};
use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::parse::Parse;
use syn::spanned::Spanned;
use syn::{Error, Token, parse_macro_input};

use crate::formulas::parser::{
    ArgItem, Ast, BangedContent, BangedContentInner, BangedContentKind, FunAppAst, QuantifierAst,
    QuantifierKind, VarBinding, VarBindings,
};

struct MacroInput {
    /// The path for the constructor
    ///
    /// It expects:
    /// - `mk_app: MacroFunction -> (args: [MacroExpr]) -> L`
    /// - `mk_quantifier: MacroBinder -> [MVar] -> (args: [MacroExpr]) -> MacroExpr`
    /// - `mk_variable: [MVar] -> L`
    /// - the `fresh` macro to spawn new variable
    /// - `MacroExpr`
    /// - `MacroVar`
    /// - `MacroFunction`
    /// - `MacroBinder`
    ///
    /// With `const` names in between for the const option
    path: syn::Path,
    /// Whether to try to make it const
    is_const_ast: Option<Token![const]>,
    /// The ast
    content: Ast,
}

enum Kind {
    Var,
    Formula,
    Function,
    Binder,
}

struct ArrayLike {
    kind: Kind,
    tokens: TokenStream,
    len: Option<usize>,
}

pub trait ToTokenWithInputs {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream>;
}

pub trait ToArrayWithInputs {
    fn to_array(&self, macro_input: &MacroInput) -> syn::Result<ArrayLike>;
}

impl ToTokenWithInputs for Kind {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let path = &macro_input.path;
        Ok(match self {
            Kind::Var => quote!(#path::MacroVar),
            Kind::Formula => quote!(#path::MacroExpr),
            Kind::Function => quote!(#path::MacroFunction),
            Kind::Binder => quote!(#path::MacroBinder),
        })
    }
}

impl ToTokenWithInputs for ArrayLike {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let span = self.tokens.span();
        let tokens = &self.tokens;
        if macro_input.is_const() {
            let kind = self.kind.to_tokens(&macro_input)?;
            Ok(quote_spanned! { span =>
              {
                static TMP : &'static [#kind] = &#tokens;
                TMP
              }
            })
        } else {
            Ok(quote! {#tokens})
        }
    }
}

impl Parse for MacroInput {
    fn parse(input: syn::parse::ParseStream<'_>) -> syn::Result<Self> {
        let path = input.parse()?;
        let _: Token![;] = input.parse()?;
        let is_const_ast = input.parse()?;
        let content = input.parse()?;
        Ok(Self {
            path,
            is_const_ast,
            content,
        })
    }
}

impl MacroInput {
    #[must_use]
    fn is_const(&self) -> bool {
        self.is_const_ast.is_some()
    }

    fn expr_type(&self) -> TokenStream {
        let path = &self.path;
        quote! {#path::MacroExpr}
    }

    fn mk_clone(&self, stream: &TokenStream) -> TokenStream {
        if self.is_const() {
            quote!(#stream.const_clone())
        } else {
            quote!(#stream.clone())
        }
    }

    fn and_fun(&self) -> TokenStream {
        let path = &self.path;
        quote!(&#path::AND)
    }

    fn or_fun(&self) -> TokenStream {
        let path = &self.path;
        quote!(&#path::OR)
    }

    fn eq_fun(&self) -> TokenStream {
        let path = &self.path;
        quote!(&#path::EQ)
    }

    fn neq_fun(&self) -> TokenStream {
        let path = &self.path;
        quote!(&#path::NEQ)
    }

    fn mk_true(&self) -> TokenStream {
        let t = self.expr_type();
        quote!(#t::True())
    }

    fn mk_false(&self) -> TokenStream {
        let t = self.expr_type();
        quote!(#t::False())
    }

    fn mk_ands(&self, args: impl IntoIterator<Item = TokenStream>) -> syn::Result<TokenStream> {
        let and_f = self.and_fun();
        args.into_iter().try_fold(self.mk_true(), |acc, arg| {
            FunAppAst::mk_app(self, &and_f, [acc, arg])
        })
    }

    fn mk_ors(&self, args: impl IntoIterator<Item = TokenStream>) -> syn::Result<TokenStream> {
        let and_f = self.or_fun();
        args.into_iter().try_fold(self.mk_false(), |acc, arg| {
            FunAppAst::mk_app(self, &and_f, [acc, arg])
        })
    }

    fn mk_eqs(&self, span: Span, args: &[TokenStream]) -> syn::Result<TokenStream> {
        // let args = args.into_iter().collect_vec();
        let mut args = args.iter().into_iter().multipeek();
        if args.peek().is_some() && args.peek().is_some() {
            let fun = self.eq_fun();
            let args: Vec<_> = args
                .cloned()
                .tuple_combinations()
                .map(|(a, b)| FunAppAst::mk_app(self, &fun, [a, b]))
                .try_collect()?;
            self.mk_ands(args)
        } else {
            Err(Error::new(span, "need at least two arguments to `=`"))
        }
    }

    fn mk_neqs(&self, span: Span, args: &[TokenStream]) -> syn::Result<TokenStream> {
        // let args = args.into_iter().collect_vec();
        let mut args = args.iter().into_iter().multipeek();
        if args.peek().is_some() && args.peek().is_some() {
            let fun = self.neq_fun();
            let args: Vec<_> = args
                .cloned()
                .tuple_combinations()
                .map(|(a, b)| FunAppAst::mk_app(self, &fun, [a, b]))
                .try_collect()?;
            self.mk_ands(args)
        } else {
            Err(Error::new(span, "need at least two arguments to `=`"))
        }
    }
}

impl ToTokenWithInputs for Ast {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let path = &macro_input.path;
        match &self.inner {
            super::parser::InnerAst::Quantifier(quantifier_ast) => {
                quantifier_ast.to_tokens(macro_input)
            }
            super::parser::InnerAst::True => Ok(macro_input.mk_true()),
            super::parser::InnerAst::False => Ok(macro_input.mk_false()),
            super::parser::InnerAst::And(args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|x| x.to_tokens(macro_input))
                    .try_collect()?;
                if macro_input.is_const() {
                    macro_input.mk_ands(args)
                } else {
                    Ok(quote!(#path::mk_ands(::itertools::chain![#(#args),*])))
                }
            }
            super::parser::InnerAst::Or(args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|x| x.to_tokens(macro_input))
                    .try_collect()?;
                if macro_input.is_const() {
                    macro_input.mk_ors(args)
                } else {
                    Ok(quote!(#path::mk_ors(::itertools::chain![#(#args),*])))
                }
            }
            super::parser::InnerAst::Eq(args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|x| x.to_tokens(macro_input))
                    .try_collect()?;
                if macro_input.is_const() {
                    macro_input.mk_eqs(self.span, &args)
                } else {
                    Ok(quote!(#path::mk_eqs(::itertools::chain![#(#args),*])))
                }
            }
            super::parser::InnerAst::Neq(args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|x| x.to_tokens(macro_input))
                    .try_collect()?;
                if macro_input.is_const() {
                    macro_input.mk_neqs(self.span, &args)
                } else {
                    Ok(quote!(#path::mk_neqs(::itertools::chain![#(#args),*])))
                }
            }
            super::parser::InnerAst::Not(ast) => {
                let ast = ArgItem::to_token_regular(ast, macro_input)?;
                FunAppAst::mk_app(macro_input, &quote!(#path::NOT), [ast])
            }
            super::parser::InnerAst::Implies(ast, ast1) => {
                let ast = ArgItem::to_token_regular(ast, macro_input)?;
                let ast1 = ArgItem::to_token_regular(ast1, macro_input)?;
                FunAppAst::mk_app(macro_input, &quote!(#path::IMPLIES), [ast, ast1])
            }
            super::parser::InnerAst::FunApp(fun_app_ast) => fun_app_ast.to_tokens(macro_input),
            super::parser::InnerAst::Banged(banged_content) => {
                banged_content.to_tokens(macro_input)
            }
        }
    }
}

impl ToTokenWithInputs for QuantifierKind {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let path = &macro_input.path;
        Ok(match self {
            QuantifierKind::Forall(s) => quote_spanned!(s.span() => #path::MacroBinder::Forall),
            QuantifierKind::Exists(s) => quote_spanned!(s.span() => #path::MacroBinder::Exists),
            QuantifierKind::FindSuchThat(s) => {
                quote_spanned!(s.span() => #path::MacroBinder::FindSuchThat)
            }
        })
    }
}

impl ToTokenWithInputs for ArgItem {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        match self {
            ArgItem::Regular(ast) => Self::to_token_regular(ast, macro_input),
            ArgItem::SplatExpr(expr) if !macro_input.is_const() => Ok(quote!({#expr})),
            ArgItem::SplatIdent(ident) if !macro_input.is_const() => Ok(quote!({#ident})),
            e => Err(Error::new(e.span(), "no splat expression allowed in const")),
        }
    }
}

impl ArgItem {
    pub fn to_token_regular(ast: &Ast, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let ast = ast.to_tokens(macro_input)?;
        if macro_input.is_const() {
            Ok(ast)
        } else {
            Ok(quote!(::std::iter::once(#ast)))
        }
    }
}

impl ToTokenWithInputs for VarBinding {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let cons_token = &macro_input.is_const_ast;
        let path = &macro_input.path;
        let sort = &self.sort;

        Ok(quote!(#path::fresh!(#cons_token #sort)))
    }
}

impl ToTokenWithInputs for QuantifierAst {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let Self { kind, body, .. } = self;

        let BindingForQuantifer {
            pre_binding,
            binding_arg,
        } = self.mk_bindings(macro_input)?;

        let path = &macro_input.path;
        let kind = kind.to_tokens(macro_input)?;
        let args: Vec<_> = body
            .iter()
            .map(|x| x.to_tokens(macro_input))
            .try_collect()?;

        let constructor;
        let nargs;
        if macro_input.is_const() {
            let t = Kind::Formula.to_tokens(macro_input)?;
            constructor = quote!(#path::mk_const_quantifier);
            nargs = quote!({static TMP: &'static [#t] = [#(#args),*]; TMP})
        } else {
            constructor = quote!(#path::mk_quantifier);
            nargs = quote!(::itertools::chain![#(#args),*])
        };

        Ok(quote! {{
          #pre_binding
          #constructor(#kind, #binding_arg, {
            // compute the argument
            #nargs
          })
        }})
    }
}

struct BindingForQuantifer {
    pre_binding: Option<TokenStream>,
    binding_arg: TokenStream,
}

impl QuantifierAst {
    fn mk_bindings(&self, macro_input: &MacroInput) -> Result<BindingForQuantifer, Error> {
        let ic = macro_input.is_const();
        let path = &macro_input.path;
        let pre_binding;
        let binding_arg;
        match &self.bindings {
            VarBindings::Ident(ident) => {
                pre_binding = None;
                binding_arg = if ic {
                    quote!(#ident)
                } else {
                    quote!(#ident.clone())
                };
            }
            VarBindings::Expr(expr) => {
                pre_binding = None;
                binding_arg = quote! {{#expr}};
            }
            VarBindings::Binding(var_bindings) => {
                let names = var_bindings
                    .iter()
                    .map(|VarBinding { name, .. }| quote!(#name))
                    .collect_vec();
                let binding: Vec<_> = var_bindings
                    .iter()
                    .map(|x| x.to_tokens(macro_input))
                    .try_collect()?;
                let t = Kind::Var.to_tokens(macro_input)?;
                let keyword = if ic { quote!(static) } else { quote!(let) };
                let names_declarations = {
                    izip!(&names, &binding).map(|(ident, content)| {
                        quote! {#keyword #ident: #t = #content; }
                    })
                };
                let mk_formula_from_var = quote!(#path::mk_var);

                pre_binding = Some(quote!(#(#names_declarations)*));
                if ic {
                    binding_arg = quote! {{
                      static TMP : &'static [#t] = [#(#names.const_clone()),*];
                      TMP
                    }}
                } else {
                    binding_arg = quote!([#(#names.clone()),*]);
                }
                let t = Kind::Formula.to_tokens(macro_input)?;
            }
        }

        Ok(BindingForQuantifer {
            pre_binding,
            binding_arg,
        })
    }
}

impl ToTokenWithInputs for FunAppAst {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let Self { func, args } = self;
        let args: Vec<_> = args
            .iter()
            .map(|arg| arg.to_tokens(macro_input))
            .try_collect()?;
        Self::mk_app(macro_input, &quote!(#func), args)
    }
}

impl FunAppAst {
    fn mk_app(
        macro_input: &MacroInput,
        fun: &TokenStream,
        args: impl IntoIterator<Item = TokenStream>,
    ) -> Result<TokenStream, Error> {
        let constuctor;
        let nargs;
        let path = &macro_input.path;
        let args = args.into_iter();
        let fun = macro_input.mk_clone(fun);
        let borrow;
        if macro_input.is_const() {
            let t = Kind::Formula.to_tokens(macro_input)?;
            constuctor = quote!(#path::mk_const_app);
            nargs = quote!({static TMP: &'static [#t] = &[#(#args),*]; TMP});
            borrow = None
        } else {
            constuctor = quote!(#path::mk_app);
            nargs = quote!(::itertools::chain![#(#args),*]);
            borrow = Some(quote!(&));
        }
        Ok(quote!(#constuctor(#borrow #fun, #nargs)))
    }
}

impl ToTokenWithInputs for BangedContent {
    fn to_tokens(&self, macro_input: &MacroInput) -> syn::Result<TokenStream> {
        let path = &macro_input.path;
        let Self { kind, inner } = self;
        let ret = match inner {
            BangedContentInner::Ident(ident) => {
                let cloned = macro_input.mk_clone(&quote!(#ident));
                if macro_input.is_const() {
                    match kind {
                        BangedContentKind::ExplamationMark(_) => {
                            quote!(#path::mk_var_from_ref(&#ident))
                        }
                        BangedContentKind::Cross(_) => cloned,
                    }
                } else {
                    quote!(#cloned.into())
                }
            }
            BangedContentInner::Expr(expr) => match kind {
                BangedContentKind::ExplamationMark(_) => quote!(#path::mk_var({#expr})),
                BangedContentKind::Cross(_) => quote!({#expr}),
            },
        };

        // if !macro_input.is_const() {
        //     ret = quote!(::std::iter::once(#ret))
        // }
        Ok(ret)
    }
}

pub fn mk_recexpr(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let macro_input = parse_macro_input!(input as MacroInput);
    let output: proc_macro::TokenStream =
        macro_input.content.to_tokens(&macro_input).unwrap().into();
    output
}
