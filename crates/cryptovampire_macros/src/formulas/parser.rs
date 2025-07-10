use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{format_ident, quote, ToTokens}; // format_ident is key here
use syn::token::Paren;
use syn::{parenthesized, Error};
use syn::{
    parse::{Parse, ParseStream, Result},
    parse_macro_input,
    token,
    Expr,
    Ident,
    Lit,
    LitBool,
    LitInt,
    LitStr, // LitStr might not be needed if FunApp changed
    Path,
    Token,
};
use utils::ereturn_if;

pub enum QuantifierKind {
    Forall,
    Exists,
}

pub enum InnerAst {
    Quantifier {
        kind: QuantifierKind,
        bindings: VarBindings,
        body: Box<Ast>,
    },
    True,
    False,
    And(ArgsVec),
    Or(ArgsVec),
    Eq(ArgsVec),
    Neq(ArgsVec),
    Not(Box<Ast>),
    Implies(Box<Ast>, Box<Ast>),
    FunApp {
        func: FunIdent,
        args: ArgsVec,
    },
    Banged(BangedContent),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum FunIdent {
    Ident(Ident),
    Path(Path),
}

pub struct Ast {
    pub span: Span,
    pub inner: InnerAst,
}

pub enum VarBindings {
    Ident(Ident),
    Expr(Expr),
    Binding(Vec<VarBinding>),
}

pub struct VarBinding {
    pub name: VarName,
    pub index: VarIndex, // Can now be an expression
    pub sort: Expr,
}

pub enum VarName {
    Underscore(Token![_]),
    Ident(Ident),
}

pub enum BangedContent {
    // Represents content after a '#'
    Lit(Lit),
    Ident(Ident),
    Expr(Expr),
}

pub enum VarIndex {
    // Represents the SMT variable index
    Lit(LitInt),
    Expr(Expr),
    Ident(Ident),
}

pub enum ArgItem {
    Regular(Ast),      // A standard SMT expression
    SplatExpr(Expr),   // Represents #(expr)*
    SplatIdent(Ident), // Represents #ident*
}

// Args is now a list of ArgItems
pub type ArgsVec = Vec<ArgItem>;

impl InnerAst {
    pub fn with(self, span: Span) -> Ast {
        Ast { span, inner: self }
    }
}

impl Parse for FunIdent {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Ident) {
            Ok(Self::Ident(input.parse()?))
        } else {
            Ok(Self::Path(input.parse()?))
        }
    }
}

impl From<Ident> for FunIdent {
    fn from(v: Ident) -> Self {
        Self::Ident(v)
    }
}

impl From<Path> for FunIdent {
    fn from(v: Path) -> Self {
        Self::Path(v)
    }
}

impl ToTokens for FunIdent {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            FunIdent::Ident(ident) => ident.to_tokens(tokens),
            FunIdent::Path(path) => path.to_tokens(tokens),
        }
    }
}

impl Parse for BangedContent {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        // '#' is expected to be consumed by the caller before calling this
        // If not, add input.parse::<Token![#]>()?; here.
        // Based on your ParsedSmt::parse, '#' is consumed before calling this parse.
        if input.peek(token::Paren) {
            let content;
            parenthesized!(content in input);
            let expr: Expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("Expected end of expression in #()"));
            }
            Ok(BangedContent::Expr(expr))
        } else if input.peek(Lit) {
            let lit: Lit = input.parse()?;
            Ok(BangedContent::Lit(lit))
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            Ok(BangedContent::Ident(ident))
        } else {
            Err(input.error("Expected literal, identifier, or parenthesized expression after #"))
        }
    }
}

impl Parse for VarIndex {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(token::Paren) {
            let content;
            parenthesized!(content in input);
            let expr: Expr = content.parse()?;
            if !content.is_empty() {
                return Err(content.error("Expected end of expression in () for variable index"));
            }
            Ok(Self::Expr(expr))
        } else if input.peek(LitInt) {
            // Specifically LitInt for indices
            let lit = input.parse()?;
            Ok(Self::Lit(lit))
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            Ok(Self::Ident(ident))
        } else {
            Err(input.error("Expected integer literal, identifier, or parenthesized expression for variable index"))
        }
    }
}

impl Parse for ArgItem {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![#]) {
            // Tentatively parse '#', but fork to give it back if not a splat or specific #term
            let marker_span = input.cursor().span(); // For error messages
            input.parse::<Token![#]>()?; // Consume '#'

            if input.peek(token::Paren) {
                // Potential #(expr) or #(expr)*
                input.span();
                let expr_content;
                let span = parenthesized!(expr_content in input).span.join();
                let expr: Expr = expr_content.parse().inspect_err(|_| {
                    eprintln!("{input}");
                })?;
                if !expr_content.is_empty() {
                    return Err(expr_content.error("Trailing tokens in #(...) part of argument"));
                }

                if input.peek(Token![*]) {
                    input.parse::<Token![*]>()?; // Consume '*'
                    Ok(ArgItem::SplatExpr(expr))
                } else {
                    // Regular #(expr) term
                    Ok(ArgItem::Regular(
                        InnerAst::Banged(BangedContent::Expr(expr)).with(span),
                    ))
                }
            } else if input.peek(Ident) {
                // Potential #ident or #ident*
                let ident: Ident = input.parse()?;
                if input.peek(Token![*]) {
                    input.parse::<Token![*]>()?; // Consume '*'
                    Ok(ArgItem::SplatIdent(ident))
                } else {
                    // Regular #ident term
                    let span = ident.span();
                    Ok(ArgItem::Regular(
                        InnerAst::Banged(BangedContent::Ident(ident)).with(span),
                    ))
                }
            } else if input.peek(Lit) {
                // Regular #lit term
                let lit: Lit = input.parse()?;
                let span = lit.span();
                Ok(ArgItem::Regular(
                    InnerAst::Banged(BangedContent::Lit(lit)).with(span),
                ))
            } else {
                Err(syn::Error::new(
                    marker_span,
                    "Expected '(', identifier, or literal after # in argument list",
                ))
            }
        } else {
            // Not starting with #, so it's a regular ParsedSmt (e.g., sub-expression like (foo), true, false, or plain_ident)
            Ok(ArgItem::Regular(input.parse::<Ast>()?))
        }
    }
}

impl From<Ast> for ArgItem {
    fn from(v: Ast) -> Self {
        Self::Regular(v)
    }
}

// This function will parse a list of ArgItems for functions/operators
fn parse_argument_list(input: ParseStream<'_>) -> Result<ArgsVec> {
    let mut items = Vec::new();
    while !input.is_empty() {
        items.push(input.parse::<ArgItem>()?);
    }
    Ok(items)
}

// fn parse_smt_list_content(input: ParseStream<'_>) -> Result<Vec<ParsedSmt>> {
//     let mut args = Vec::new();
//     while !input.is_empty() {
//         args.push(input.parse()?);
//     }
//     Ok(args)
// }

fn parse_bindings(input: ParseStream<'_>) -> Result<Vec<VarBinding>> {
    let content;
    parenthesized!(content in input);
    let mut bindings = Vec::new();
    while !content.is_empty() {
        bindings.push(content.parse()?);
    }
    Ok(bindings)
}

impl Parse for VarName {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![_]) {
            Ok(Self::Underscore(input.parse()?))
        } else {
            Ok(Self::Ident(input.parse()?))
        }
    }
}

impl Parse for VarBinding {
    fn parse(content: ParseStream<'_>) -> Result<Self> {
        let binding_content;
        parenthesized!(binding_content in content);

        binding_content.parse::<Token![#]>()?;
        let name: VarName = binding_content.parse()?;
        binding_content.parse::<Token![!]>()?;
        let index: VarIndex = binding_content.parse()?; // Use VarIndex parser
        let sort: Expr = binding_content.parse()?;
        Ok(VarBinding { name, index, sort })
    }
}

impl Parse for VarBindings {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![#]) {
            input.parse::<Token![#]>()?;
            if input.peek(token::Paren) {
                let content;
                parenthesized!(content in input);
                let expr: Expr = content.parse()?;
                ereturn_if!(
                    !content.is_empty(),
                    Err(content.error("Expected end of expression in #()"))
                );

                Ok(Self::Expr(expr))
            } else if input.peek(Ident) {
                let ident: Ident = input.parse()?;
                Ok(Self::Ident(ident))
            } else {
                Err(input
                    .error("Expected literal, identifier, or parenthesized expression after #"))
            }
        } else {
            Ok(Self::Binding(parse_bindings(input)?))
        }
    }
}

impl Parse for Ast {
    fn parse(input: ParseStream<'_>) -> Result<Ast> {
        if input.peek(Token![#]) {
            input.parse::<Token![#]>()?; // Consume '#'
            let span = input.span();
            let banged_content = input.parse::<BangedContent>()?;
            return Ok(InnerAst::Banged(banged_content).with(span));
        }

        if input.peek(token::Paren) {
            let content;
            let span = parenthesized!(content in input).span.join();
            ereturn_if!(
                content.is_empty(),
                Err(input.error("Empty parentheses are not valid SMT formula"))
            );

            if content.peek(Token![=>]) {
                content.parse::<Token![=>]>()?;
                // let [a, b] = parse_smt_list_content(&content)?
                //     .try_into()
                //     .map_err(|_| content.error("wrong number of argument for implies"))?;
                let a = content.parse()?;
                let b = content.parse()?;
                Ok(InnerAst::Implies(Box::new(a), Box::new(b)))
            } else if content.peek(Token![=]) {
                // equality is not an ident
                content.parse::<Token![=]>()?;
                Ok(InnerAst::Eq(parse_argument_list(&content)?))
                // Ok(ParsedSmt::Eq(content.parse()?))
            } else if content.peek(Ident) {
                // the rest
                let keyword: Ident = content.parse()?;
                match keyword.to_string().as_str() {
                    s @ ("forall" | "exists") => {
                        let kind = match s {
                            "forall" => QuantifierKind::Forall,
                            "exists" => QuantifierKind::Exists,
                            _ => unreachable!("the string changed??? {s}"),
                        };
                        let bindings = content.parse()?;
                        let body = content.parse()?;
                        if !content.is_empty() {
                            return Err(content.error("Unexpected token after forall body"));
                        }
                        Ok(InnerAst::Quantifier {
                            kind,
                            bindings,
                            body: Box::new(body),
                        })
                    }
                    "and" => Ok(InnerAst::And(parse_argument_list(&content)?)),
                    "or" => Ok(InnerAst::Or(parse_argument_list(&content)?)),
                    "distinct" => Ok(InnerAst::Neq(parse_argument_list(&content)?)),
                    "not" => {
                        let arg = content.parse()?;
                        if !content.is_empty() {
                            return Err(content.error("Expected single argument for not"));
                        }
                        Ok(InnerAst::Not(Box::new(arg)))
                    }
                    _ => {
                        let func_ident = keyword;
                        let args = parse_argument_list(&content)?;
                        Ok(InnerAst::FunApp {
                            func: func_ident.into(),
                            args,
                        })
                    }
                }
            } else {
                Err(content.error("Expected an identifier after '('"))
            }
            .map(|x| x.with(span))
        } else if input.peek(LitBool) {
            let LitBool { value, span } = input.parse()?;
            match value {
                true => Ok(InnerAst::True),
                false => Ok(InnerAst::False),
            }
            .map(|x| x.with(span))
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            let span = ident.span();
            // ident.to_string().as_str();
            Ok(InnerAst::FunApp {
                func: ident.into(),
                args: vec![],
            })
            .map(|x| x.with(span))
        } else {
            Err(input.error("Expected SMT formula: #term, (expression), or identifier"))
        }
    }
}
