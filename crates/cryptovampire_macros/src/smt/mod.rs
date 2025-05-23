// In your proc-macro crate's src/lib.rs

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, quote}; // format_ident is key here
use syn::parenthesized;
use syn::token::Paren;
use syn::{
    parse::{Parse, ParseStream, Result},
    parse_macro_input,
    token,
    Expr,
    Ident,
    Lit,
    LitInt,
    LitStr, // LitStr might not be needed if FunApp changed
    Token,
};
use utils::ereturn_if;

// Counter for generating unique temporary variable names
static VAR_COUNTER: AtomicUsize = AtomicUsize::new(0);

enum QuantifierKind {
    Forall,
    Exists,
}

enum ParsedSmt {
    Quantifier {
        kind: QuantifierKind,
        bindings: VarBindings,
        body: Box<ParsedSmt>,
    },
    True,
    False,
    And(ArgsVec),
    Or(ArgsVec),
    Eq(ArgsVec),
    Neq(ArgsVec),
    Not(Box<ParsedSmt>),
    Implies(Box<ParsedSmt>, Box<ParsedSmt>),
    FunApp {
        func: Ident,
        args: ArgsVec,
    },
    Banged(BangedContent),
}

enum VarBindings {
    Ident(Ident),
    Expr(Expr),
    Binding(Vec<VarBinding>),
}

struct VarBinding {
    name: Ident,
    index: VarIndex, // Can now be an expression
    sort: Expr,
}

enum BangedContent {
    // Represents content after a '#'
    Lit(Lit),
    Ident(Ident),
    Expr(Expr),
}

enum VarIndex {
    // Represents the SMT variable index
    Lit(LitInt),
    Expr(Expr),
    Ident(Ident),
}

enum ArgItem {
    Regular(ParsedSmt),  // A standard SMT expression
    SplatExpr(Expr),     // Represents #(expr)*
    SplatIdent(Ident),   // Represents #ident*
}

// Args is now a list of ArgItems
type ArgsVec = Vec<ArgItem>;


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

            if input.peek(token::Paren) { // Potential #(expr) or #(expr)*
                let expr_content;
                parenthesized!(expr_content in input);
                let expr: Expr = expr_content.parse()?;
                if !expr_content.is_empty() {
                    return Err(expr_content.error("Trailing tokens in #(...) part of argument"));
                }

                if input.peek(Token![*]) {
                    input.parse::<Token![*]>()?; // Consume '*'
                    Ok(ArgItem::SplatExpr(expr))
                } else {
                    // Regular #(expr) term
                    Ok(ArgItem::Regular(ParsedSmt::Banged(BangedContent::Expr(expr))))
                }
            } else if input.peek(Ident) { // Potential #ident or #ident*
                let ident: Ident = input.parse()?;
                if input.peek(Token![*]) {
                    input.parse::<Token![*]>()?; // Consume '*'
                    Ok(ArgItem::SplatIdent(ident))
                } else {
                    // Regular #ident term
                    Ok(ArgItem::Regular(ParsedSmt::Banged(BangedContent::Ident(ident))))
                }
            } else if input.peek(Lit) { // Regular #lit term
                let lit: Lit = input.parse()?;
                Ok(ArgItem::Regular(ParsedSmt::Banged(BangedContent::Lit(lit))))
            } else {
                Err(syn::Error::new(marker_span, "Expected '(', identifier, or literal after # in argument list"))
            }
        } else {
            // Not starting with #, so it's a regular ParsedSmt (e.g., sub-expression like (foo), true, false, or plain_ident)
            Ok(ArgItem::Regular(input.parse::<ParsedSmt>()?))
        }
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

impl Parse for VarBinding {
    fn parse(content: ParseStream<'_>) -> Result<Self> {
        let binding_content;
        parenthesized!(binding_content in content);

        binding_content.parse::<Token![#]>()?;
        let name: Ident = binding_content.parse()?;
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

impl Parse for ParsedSmt {
    fn parse(input: ParseStream<'_>) -> Result<ParsedSmt> {
        if input.peek(Token![#]) {
            input.parse::<Token![#]>()?; // Consume '#'
            let banged_content = input.parse::<BangedContent>()?;
            return Ok(Self::Banged(banged_content));
        }

        if input.peek(token::Paren) {
            let content;
            parenthesized!(content in input);
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
                Ok(ParsedSmt::Implies(Box::new(a), Box::new(b)))
            } else if content.peek(Token![=]) {
                // equality is not an ident
                content.parse::<Token![=]>()?;
                Ok(ParsedSmt::Eq(parse_argument_list(&content)?))
                // Ok(ParsedSmt::Eq(content.parse()?))
            } else if content.peek(Ident) {
                // the rest
                let keyword: Ident = content.parse()?;
                match keyword.to_string().as_str() {
                    s @ ("forall" | "exists") => {
                        let kind = match s {
                            "forall" => QuantifierKind::Forall,
                            "exists" => QuantifierKind::Exists,
                            _ => unreachable!(),
                        };
                        let bindings = content.parse()?;
                        let body = content.parse()?;
                        if !content.is_empty() {
                            return Err(content.error("Unexpected token after forall body"));
                        }
                        Ok(ParsedSmt::Quantifier {
                            kind,
                            bindings,
                            body: Box::new(body),
                        })
                    }
                    "and" => Ok(ParsedSmt::And(parse_argument_list(&content)?)),
                    "or" => Ok(ParsedSmt::Or(parse_argument_list(&content)?)),
                    "distinct" => Ok(ParsedSmt::Neq(parse_argument_list(&content)?)),
                    "not" => {
                        let arg = content.parse()?;
                        if !content.is_empty() {
                            return Err(content.error("Expected single argument for not"));
                        }
                        Ok(ParsedSmt::Not(Box::new(arg)))
                    }
                    _ => {
                        let func_ident = keyword;
                        let args = parse_argument_list(&content)?;
                        Ok(ParsedSmt::FunApp {
                            func: func_ident,
                            args,
                        })
                    }
                }
            } else {
                Err(content.error("Expected an identifier after '('"))
            }
        } else if input.peek(Ident) {
            let ident: Ident = input.parse()?;
            match ident.to_string().as_str() {
                "true" => Ok(ParsedSmt::True),
                "false" => Ok(ParsedSmt::False),
                _ => Ok(ParsedSmt::FunApp {
                    func: ident,
                    args: vec![],
                }),
            }
        } else {
            Err(input.error("Expected SMT formula: #term, (expression), or identifier"))
        }
    }
}

fn generate_banged_expr_tokens(b: BangedContent) -> proc_macro2::TokenStream {
    match b {
        BangedContent::Lit(lit) => quote! { #lit },
        BangedContent::Ident(ident) => quote! { #ident.clone() },
        BangedContent::Expr(expr) => quote! { (#expr) }, // Parenthesize expr just in case
    }
}

fn generate_var_index_expr_tokens(v_idx: &VarIndex) -> proc_macro2::TokenStream {
    match v_idx {
        VarIndex::Lit(lit_int) => quote! { #lit_int },
        VarIndex::Expr(expr) => quote! { (#expr) }, // Parenthesize expr
        VarIndex::Ident(ident) => quote! { #ident.clone() },
    }
}

// fn generate_args(parsed: Args) -> proc_macro2::TokenStream {
//     match parsed {
//         Args::Expr(expr) => quote! { (#expr).into_iter().collect() },
//         Args::Ident(ident) => quote! { #ident.into_iter().collect() },
//         Args::Other(args) => {
//             let args = args.into_iter().map(generate_code);
//             quote! {vec![#(#args),*]}
//         },
//     }
// }

fn generate_args(items: ArgsVec) -> proc_macro2::TokenStream {
    // let vec_builder_ident = format_ident!(
    //     "__smt_args_vec_{}",
    //     VAR_COUNTER.fetch_add(1, Ordering::Relaxed),
    //     span = proc_macro2::Span::call_site()
    // );

    let mut construction_statements = Vec::new();
    // construction_statements.push(quote! { let mut #vec_builder_ident = Vec::new(); });

    for item in items {
        match item {
            ArgItem::Regular(smt) => {
                let smt_code = generate_code(smt); // generate_code returns code for one SmtFormula
                construction_statements.push(quote! { [#smt_code] });
            }
            ArgItem::SplatExpr(expr_to_splat) => {
                // Assume expr_to_splat evaluates to an iterable of items convertible to SmtFormula
                construction_statements.push(
                    quote! { (#expr_to_splat).into_iter().map(|item| item.into()) },
                );
            }
            ArgItem::SplatIdent(ident_to_splat) => {
                // Assume ident_to_splat is an iterable of items convertible to SmtFormula
                construction_statements.push(
                    quote! { (#ident_to_splat).into_iter().map(|item| item.into()) },
                );
            }
        }
    }

    quote! {
        {
            ::itertools::chain![#(#construction_statements),*].collect()
        }
    }
}

fn generate_code(parsed: ParsedSmt) -> proc_macro2::TokenStream {
    let crate_path = quote! { ::cryptovampire_smt };

    match parsed {
        ParsedSmt::True => quote! { #crate_path::SmtFormula::True },
        ParsedSmt::False => quote! { #crate_path::SmtFormula::False },
        ParsedSmt::Banged(banged_content) => {
            let tokens = generate_banged_expr_tokens(banged_content);
            quote! { (#tokens).into() }
        }
        ParsedSmt::And(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::And(#processed_args) }
        }
        ParsedSmt::Or(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Or(#processed_args) }
        }
        ParsedSmt::Eq(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Eq(#processed_args) }
        }
        ParsedSmt::Neq(args) => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            quote! { #crate_path::SmtFormula::Neq(#processed_args) }
        }
        ParsedSmt::Not(arg) => {
            let processed_arg = generate_code(*arg);
            quote! { #crate_path::SmtFormula::Not(Box::new(#processed_arg)) }
        }
        ParsedSmt::Implies(a, b) => {
            let [a, b] = [*a, *b].map(generate_code);
            quote! {#crate_path::SmtFormula::Implies(Box::new(#a), Box::new(#b))}
        }
        ParsedSmt::FunApp { func, args } => {
            let processed_args = generate_args(args); //args.into_iter().map(generate_code);
            // As per your change, #func (the Ident) is passed directly.
            // This implies SmtFormula::Fun can handle an Ident or its type N in
            // SmtFormula<N,S> can be From<Ident> or similar.
            quote! { #crate_path::SmtFormula::Fun(#func.clone(), #processed_args) }
        }
        ParsedSmt::Quantifier {
            kind,
            bindings,
            body,
        } => {
            // Determine if it's Forall or Exists for the final constructor
            let constructor = match kind {
                QuantifierKind::Forall => quote! { #crate_path::SmtFormula::Forall },
                QuantifierKind::Exists => quote! { #crate_path::SmtFormula::Exists },
            };
            let processed_body = generate_code(*body);

            match bindings {
                VarBindings::Binding(bindings) => {
                    generate_quant_with_binders(crate_path, constructor, processed_body, bindings)
                }
                VarBindings::Expr(expr) => quote! {#constructor(#expr, Box::new(#processed_body))},
                VarBindings::Ident(ident) => {
                    quote! {#constructor(#ident, Box::new(#processed_body))}
                }
            }
        }
    }
}

fn generate_quant_with_binders(
    crate_path: proc_macro2::TokenStream,
    constructor: proc_macro2::TokenStream,
    processed_body: proc_macro2::TokenStream,
    bindings: Vec<VarBinding>,
) -> proc_macro2::TokenStream {
    // Generate `let __smt_idx_temp_N = index_expr; let user_var = SmtFormula::Var(__smt_idx_temp_N);`
    // And collect the __smt_idx_temp_N idents.
    let mut let_bindings = Vec::new();
    let mut temp_var_idents_for_sorted_var = Vec::new();

    for binding in bindings.iter() {
        let user_var_name = &binding.name;
        let index_eval_expr = generate_var_index_expr_tokens(&binding.index);

        let i = VAR_COUNTER.fetch_add(1, Ordering::AcqRel);
        // Create a hygienically distinct temporary variable name for the evaluated index
        let temp_index_var_ident = format_ident!(
            "__smt_idx_temp_{}",
            i,
            span = proc_macro2::Span::call_site()
        );

        let_bindings.push(quote! {
            let #temp_index_var_ident = #crate_path::VarInner::Int(#index_eval_expr);
            let #user_var_name = #crate_path::SmtFormula::Var(#temp_index_var_ident.clone());
        });
        temp_var_idents_for_sorted_var.push(temp_index_var_ident);
    }

    let sorted_vars_elements: Vec<_> = bindings
        .iter()
        .zip(temp_var_idents_for_sorted_var.iter())
        .map(|(binding, temp_idx_ident)| {
            let sort_expr = &binding.sort;
            quote! { #crate_path::SortedVar { var: #temp_idx_ident, sort: #sort_expr } }
        })
        .collect();

    quote! {
        {
            #(#let_bindings)*
            #constructor( // Use the Forall or Exists constructor
                vec![ #(#sorted_vars_elements),* ],
                Box::new(#processed_body)
            )
        }
    }
}

pub fn smt_formulas(input: TokenStream) -> TokenStream {
    let parsed_smt = parse_macro_input!(input as ParsedSmt);
    generate_code(parsed_smt).into()
}
