use std::str;

use proc_macro2::Span;
use quote::ToTokens;
use syn::spanned::Spanned;
// format_ident is key here
use syn::{Error, parenthesized};
use syn::{
    Expr,
    Ident,
    LitBool, // LitStr might not be needed if FunApp changed
    Path,
    Token,
    parse::{Parse, ParseStream, Result},
    token,
};
use utils::ereturn_if;

pub enum QuantifierKind {
    Forall(Ident),
    Exists(Ident),
    FindSuchThat(Ident),
}
impl QuantifierKind {
    pub fn ident(&self) -> &Ident {
        match self {
            QuantifierKind::Forall(ident)
            | QuantifierKind::Exists(ident)
            | QuantifierKind::FindSuchThat(ident) => ident,
        }
    }

    pub fn span(&self) -> Span {
        self.ident().span()
    }
}

pub enum InnerAst {
    Quantifier(QuantifierAst),
    True,
    False,
    And(ArgsVec),
    Or(ArgsVec),
    Eq(ArgsVec),
    Neq(ArgsVec),
    Not(Box<Ast>),
    Implies(Box<Ast>, Box<Ast>),
    FunApp(FunAppAst),
    Banged(BangedContent),
}

pub struct QuantifierAst {
    pub kind: QuantifierKind,
    pub bindings: VarBindings,
    pub body: ArgsVec,
}

pub struct FunAppAst {
    pub func: FunIdent,
    pub args: ArgsVec,
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
    // pub index: Option<VarIndex>, // Can now be an expression
    pub sort: Expr,
}

pub enum VarName {
    Underscore(Token![_]),
    Ident(Ident),
}

impl ToTokens for VarName {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            VarName::Underscore(underscore) => underscore.to_tokens(tokens),
            VarName::Ident(ident) => ident.to_tokens(tokens),
        }
    }
}

/// Represents content after a '#' or `!`
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct BangedContent {
    pub kind: BangedContentKind,
    pub inner: BangedContentInner,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BangedContentKind {
    ExplamationMark(Token![!]),
    Cross(Token![#]),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum BangedContentInner {
    // Lit(Lit),
    Ident(Ident),
    Expr(Expr),
}

pub enum VarIndex {
    // Represents the SMT variable index
    // Lit(LitInt),
    Expr(Expr),
    Ident(Ident),
}

pub enum ArgItem {
    Regular(Ast),      // A standard SMT expression
    SplatExpr(Expr),   // Represents #(expr)*
    SplatIdent(Ident), // Represents #ident*
}

impl ArgItem {
    pub fn span(&self) -> Span {
        match self {
            ArgItem::Regular(ast) => ast.span,
            ArgItem::SplatExpr(expr) => expr.span(),
            ArgItem::SplatIdent(ident) => ident.span(),
        }
    }
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

impl Parse for BangedContentInner {
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
            Ok(Self::Expr(expr))
        // } else if input.peek(Lit) {
        //     let lit: Lit = input.parse()?;
        //     Ok(Self::Lit(lit))
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            Ok(Self::Ident(ident))
        } else {
            Err(input.error("Expected literal, identifier, or parenthesized expression after #"))
        }
    }
}

impl Parse for BangedContentKind {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![#]) {
            Ok(Self::Cross(input.parse()?))
        } else {
            Ok(Self::ExplamationMark(input.parse()?))
        }
    }
}

impl Parse for BangedContent {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let kind = input.parse()?;
        let inner = input.parse()?;
        Ok(Self { kind, inner })
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
        // } else if input.peek(LitInt) {
        //     // Specifically LitInt for indices
        //     let lit = input.parse()?;
        //     Ok(Self::Lit(lit))
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            Ok(Self::Ident(ident))
        } else {
            Err(input.error(
                "Expected integer literal, identifier, or parenthesized expression for variable \
                 index",
            ))
        }
    }
}

impl Parse for ArgItem {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![#]) {
            // Tentatively parse '#', but fork to give it back if not a splat or specific #term
            let marker_span = input.cursor().span(); // For error messages
            let kind = input.parse::<Token![#]>()?; // Consume '#'

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
                        InnerAst::Banged(BangedContent {
                            kind: BangedContentKind::Cross(kind),
                            inner: BangedContentInner::Expr(expr),
                        })
                        .with(span),
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
                        InnerAst::Banged(BangedContent {
                            kind: BangedContentKind::Cross(kind),
                            inner: BangedContentInner::Ident(ident),
                        })
                        .with(span),
                    ))
                }
            // } else if input.peek(Lit) {
            //     // Regular #lit term
            //     let lit: Lit = input.parse()?;
            //     let span = lit.span();
            //     Ok(ArgItem::Regular(
            //         InnerAst::Banged(BangedContent {
            //             kind: BangedContentKind::Cross(kind),
            //             inner: BangedContentInner::Lit(lit),
            //         })
            //         .with(span),
            //     ))
            } else if input.peek(Token![!]) {
                let span = input.span();
                Ok(ArgItem::Regular(
                    InnerAst::Banged(input.parse()?).with(span),
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

struct ExclamationOrCross;

impl Parse for ExclamationOrCross {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![!]) {
            input.parse::<Token![!]>()?;
        } else if input.peek(Token![#]) {
            input.parse::<Token![#]>()?;
        } else {
            return Err(input.error("Expected '#' or '!'"));
        }
        Ok(Self)
    }
}

impl Parse for VarBinding {
    fn parse(content: ParseStream<'_>) -> Result<Self> {
        let binding_content;
        parenthesized!(binding_content in content);

        binding_content.parse::<ExclamationOrCross>()?;
        let name: VarName = binding_content.parse()?;

        binding_content.parse::<Option<Token![:]>>()?;

        let sort: Expr = binding_content.parse()?;
        Ok(VarBinding { name, sort })
    }
}

impl Parse for VarBindings {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        if input.peek(Token![!]) || input.peek(Token![#]) {
            input.parse::<ExclamationOrCross>()?;
            if input.peek(token::Paren) {
                let content;
                parenthesized!(content in input);
                let expr: Expr = content.parse()?;
                ereturn_if!(
                    !content.is_empty(),
                    Err(content.error("Expected end of expression in !()"))
                );

                Ok(Self::Expr(expr))
            } else if input.peek(Ident) {
                let ident: Ident = input.parse()?;
                Ok(Self::Ident(ident))
            } else {
                Err(input
                    .error("Expected literal, identifier, or parenthesized expression after !"))
            }
        } else {
            Ok(Self::Binding(parse_bindings(input)?))
        }
    }
}

impl Parse for QuantifierAst {
    fn parse(content: ParseStream<'_>) -> Result<Self> {
        let keyword: Ident = content.parse()?;
        let kind = match keyword.to_string().as_str() {
            "forall" => QuantifierKind::Forall(keyword),
            "exists" => QuantifierKind::Exists(keyword),
            "find_such_that" => QuantifierKind::FindSuchThat(keyword),
            s => {
                return Err(Error::new_spanned(
                    keyword,
                    format!("'{s}' is not a valid quantifier"),
                ));
            }
        };
        let bindings = content.parse()?;
        let body = parse_argument_list(content)?;
        Ok(Self {
            kind,
            bindings,
            body,
        })
    }
}

impl Parse for QuantifierKind {
    fn parse(input: ParseStream<'_>) -> Result<Self> {
        let keyword: Ident = input.parse()?;
        Ok(match keyword.to_string().as_str() {
            "forall" => QuantifierKind::Forall(keyword),
            "exists" => QuantifierKind::Exists(keyword),
            "find_such_that" => QuantifierKind::FindSuchThat(keyword),
            s => {
                return Err(Error::new_spanned(
                    keyword,
                    format!("'{s}' is not a valid quantifier"),
                ));
            }
        })
    }
}

impl QuantifierKind {
    pub fn is_quantifier_kind(str: &str) -> bool {
        matches!(str, "forall" | "exists" | "find_such_that")
    }
}

impl Parse for FunAppAst {
    fn parse(content: ParseStream<'_>) -> Result<Self> {
        let keyword: Ident = content.parse()?;
        let args = parse_argument_list(content)?;
        Ok(Self {
            func: keyword.into(),
            args,
        })
    }
}

impl Parse for Ast {
    fn parse(input: ParseStream<'_>) -> Result<Ast> {
        if input.peek(Token![#]) || input.peek(Token![!]) {
            // input.parse::<Token![#]>()?; // Consume '#'
            let span = input.span();
            let banged_content = input.parse()?;
            Ok(InnerAst::Banged(banged_content).with(span))
        } else if input.peek(token::Paren) {
            let content;
            let span = parenthesized!(content in input).span.join();
            ereturn_if!(
                content.is_empty(),
                Err(input.error("Empty parentheses are not valid SMT formula"))
            );

            if content.peek(Token![=>]) {
                content.parse::<Token![=>]>()?;
                let a = content.parse()?;
                let b = content.parse()?;
                Ok(InnerAst::Implies(Box::new(a), Box::new(b)))
            } else if content.peek(Token![=]) {
                // equality is not an ident
                content.parse::<Token![=]>()?;
                Ok(InnerAst::Eq(parse_argument_list(&content)?))
            } else if content.peek(Ident) {
                // the rest
                let content2 = content.fork();
                let keyword: Ident = content2.parse()?;
                match keyword.to_string().as_str() {
                    s if QuantifierKind::is_quantifier_kind(s) => {
                        content.parse().map(InnerAst::Quantifier)
                    }
                    "and" => {
                        let _: Ident = content.parse()?;
                        Ok(InnerAst::And(parse_argument_list(&content)?))
                    }
                    "or" => {
                        let _: Ident = content.parse()?;
                        Ok(InnerAst::Or(parse_argument_list(&content)?))
                    }
                    "distinct" => {
                        let _: Ident = content.parse()?;
                        Ok(InnerAst::Neq(parse_argument_list(&content)?))
                    }
                    "not" => {
                        let _: Ident = content.parse()?;
                        let arg = content.parse()?;
                        if !content.is_empty() {
                            return Err(content.error("Expected single argument for not"));
                        }
                        Ok(InnerAst::Not(Box::new(arg)))
                    }
                    _ => content.parse().map(InnerAst::FunApp),
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
            let span = input.span();
            input
                .parse()
                .map(|x| {
                    InnerAst::FunApp(FunAppAst {
                        func: x,
                        args: vec![],
                    })
                })
                .map(|x| x.with(span))
        } else {
            Err(input.error("Expected SMT formula: #term, (expression), or identifier"))
        }
    }
}
