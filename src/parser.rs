extern crate pest;
use std::collections::{HashMap, HashSet};

use crate::{
    formula::{
        builtins::{functions::*, types::*},
        formula::{var, Formula, CNF},
        function::Function,
        sort::Sort,
    },
    protocol::Protocol,
};

use pest::{
    error::{Error, ErrorVariant},
    iterators::Pair,
    Parser,
};
use pest_derive::Parser;

use self::macros::*;

mod macros {

    macro_rules! match_or_err {
        ($rule:path, $pair:expr; $content:block) => {{
            match $pair.as_rule() {
                $rule => $content,
                r => Err(Error::new_from_span(
                    ErrorVariant::ParsingError {
                        positives: vec![$rule],
                        negatives: vec![r],
                    },
                    $pair.as_span(),
                )),
            }
        }};
    }

    macro_rules! perr {
        ($pair:expr, $msg:expr) => {
            Err(Error::new_from_span(
                ErrorVariant::CustomError {
                    message: $msg,
                },
                $pair.as_span(),
            ))
        } ;
        ($pair:expr, $pat:literal, $($c:expr),+) => {
            perr!($pair, format!($pat, $($c,)+))
        };

        ($span:expr; $pat:literal, $($c:expr),*) => {
            Err(Error::new_from_span(
                ErrorVariant::CustomError {
                    message: format!($pat, $($c,)*),
                },
                $span,
            ))
        };
    }

    macro_rules! uerr {
        ($pair:expr, $what:literal) => {
            perr!($pair, "unknow {}: {}", $what, $pair.as_str())
        };
    }

    macro_rules! rerr {
        ($pair:expr, $what:literal) => {
            perr!($pair, "redeclaring {}: {}", $what, $pair.as_str())
        };
    }

    pub(crate) use {match_or_err, perr, rerr, uerr};
}

#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

#[derive(Debug, Default)]
struct Context<'a> {
    types: HashMap<&'a str, Sort>,
    funs: HashMap<&'a str, Function>,
    steps: HashSet<&'a str>,
}

const FORBIDDEN_NAMES: &'static [&'static str] = &[
    "subterm", "ite", "=", "<", ">", "assert", "if", "then", "else",
];

pub fn parse_protocol(str: &str) -> Result<Protocol, E> {
    let mut ctx = Context::default();

    ctx.types.extend(
        [
            (BOOL_NAME, BOOL.clone()),
            (MSG_NAME, MSG.clone()),
            (NONCE_NAME, NONCE.clone()),
        ]
        .into_iter(),
    );
    ctx.funs.extend(
        [
            (IF_THEN_ELSE_NAME, IF_THEN_ELSE.clone()),
            (AND_NAME, AND.clone()),
            (OR_NAME, OR.clone()),
            (NOT_NAME, NOT.clone()),
            (NONCE_MSG_NAME, NONCE_MSG.clone()),
            (TRUE_NAME, TRUE.clone()),
            (FALSE_NAME, FALSE.clone()),
        ]
        .into_iter(),
    );

    let c = MainParser::parse(Rule::content, str)?.next().unwrap();
    println!("{:?}", c);

    // for command in c.into_inner() {
    //     match command.as_rule() {
    //         Rule::declare_type => {
    //             let mut inner_rules = command.into_inner();
    //             let ident = inner_rules.next().unwrap().as_str();
    //             ftypes.insert(ident.to_owned());
    //         }
    //         _ => (),
    //     }
    // }

    todo!()
}

fn parse_type(ctx: &Context, p: Pair<Rule>) -> Result<Sort, E> {
    match_or_err!(Rule::type_name, p; {
        match ctx.types.get(p.as_str()) {
            Some(f) => Ok(f.clone()),
            _ => uerr!(p, "type")
        }
    })
}

fn parse_function_name(ctx: &Context, p: Pair<Rule>) -> Result<Function, E> {
    match_or_err!(Rule::function, p; {
        match ctx.funs.get(p.as_str()) {
            Some(f) => Ok(f.clone()),
            _ => uerr!(p, "function")
        }
    })
}

fn parse_variable<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
) -> Result<Formula, E> {
    match_or_err!(Rule::variable, p; {
        match memory.get(p.as_str()) {
            Some(var) => Ok(var.clone()),
            _ => uerr!(p, "variable")
        }
    })
}

fn parse_variable_binding<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Formula>,
) -> Result<Formula, E> {
    match_or_err!(Rule::variable_binding, p ; {
        let mut inner_rule = p.into_inner();

        let var = inner_rule.next().unwrap(); // can't fail
        let var = {
            match_or_err!(Rule::variable, var; {
                if ctx.funs.contains_key(var.as_str()) {
                    perr!(var, "the name '{}' is used for both a variable and a function", var.as_str())
                } else {
                    Ok(var.as_str())
                }
            })
        }?;

        let var_type = inner_rule.next().unwrap(); // can't fail
        let var_type = parse_type(ctx, var_type)?;

        let var_f = var!(memory.len(), var_type);
        memory.insert(var, var_f.clone());
        Ok(var_f)
    })
}

fn parse_step_name<'a>(ctx: &Context<'a>, p: Pair<'a, Rule>) -> Result<&'a str, E> {
    match_or_err!(Rule::step_name, p; {
        if ctx.steps.contains(p.as_str()) {
            rerr!(p, "step")
        } else {
            Ok(p.as_str())
        }
    })
}

fn parse_declare_function_args<'a>(ctx: &Context<'a>, p: Pair<'a, Rule>) -> Result<Vec<Sort>, E> {
    match_or_err!(Rule::type_name, p; {
        let mut inner_rule = p.into_inner();
        inner_rule.map(|p2| parse_type(ctx, p2)).collect()
    })
}

fn parse_declare_type<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<(), E> {
    match_or_err!(Rule::declare_type, p; {
        let t = p.as_str();
        if ctx.types.contains_key(t){
            rerr!(p, "type")
        } else {
            ctx.types.insert(t, t.into());
            Ok(())
        }
    })
}

fn parse_declare_function<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<(), E> {
    match_or_err!(Rule::declare_function, p; {
        let mut inner_rule = p.into_inner();

        let name_rule = inner_rule.next().unwrap();
        let name = name_rule.as_str(); // never fails
        let input_sorts = parse_declare_function_args(ctx, inner_rule.next().unwrap())?;
        let output_sort = parse_type(ctx, inner_rule.next().unwrap())?;

        match ctx.funs.get(name) {
            None => {
                let f = Function::new(name, input_sorts, output_sort);
                ctx.funs.insert(name, f);
                Ok(())
            },
            _ => perr!(name_rule, "redeclaring function: {}", name)
        }
    })
}

fn parse_application<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
) -> Result<Formula, E> {
    match_or_err!(Rule::application, p; {
        let span = p.as_span();

        let mut inner_rule = p.into_inner();

        let name = inner_rule.next().unwrap(); // can't fail
        match memory.get(name.as_str()) {
            Some(var) => {
                if inner_rule.next().is_none() {
                    Ok(var.clone())
                } else {
                    perr!(span; "a varibale is not a function",)
                }
            }
            _ => {
                let fun = match ctx.funs.get(name.as_str()) {
                    None => {
                        if inner_rule.next().is_none() {
                            return uerr!(name, "constant or variable")
                        } else {
                            return uerr!(name, "function")
                        }
                    }
                    Some(fun) => {
                        fun
                    }
                };
                let mut i = 1;

                let args: Result<Vec<_>,_> = fun.get_input_sorts().iter().map(|s|{
                    match inner_rule.next() {
                        None => perr!(span; "not enough arguments, expected {} got {}", fun.arity(), i),
                        Some(arg) => {
                            i += 1;
                            parse_term_as_type(ctx, arg, memory, s)
                        }
                    }
                }).collect();
                let args = args?;

                if inner_rule.next().is_some() {
                    perr!(span; "too many arguments, expected {} got {}", fun.arity(), i)
                } else {
                    let formula = Formula::Fun(fun.clone(), args);
                    if formula.get_sort() == &NONCE.clone() {
                        Ok(Formula::Fun(NONCE_MSG.clone(), vec![formula]))
                    } else {
                        Ok(formula)
                    }
                }
            }
        }
    })
}

fn parse_term_as_type<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
    mtype: &Sort,
) -> Result<Formula, E> {
    let span = p.as_span();
    let r = parse_term(ctx, p, memory)?;
    if r.get_sort() == mtype {
        Ok(r)
    } else {
        perr!(span; "wrong type, expected {} got {}", mtype, r.get_sort())
    }
}

fn parse_if_then_else<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
) -> Result<Formula, E> {
    match_or_err!(Rule::if_then_else, p; {
        let mut inner_rule = p.into_inner();

        let condition = parse_cnf(ctx, inner_rule.next().unwrap(), memory)?;
        let left = parse_term_as_type(ctx, inner_rule.next().unwrap(), memory, &MSG)?;
        let right = parse_term_as_type(ctx, inner_rule.next().unwrap(), memory, &MSG)?;

        let condition = todo!();

        Ok(Formula::Fun(ctx.funs.get(IF_THEN_ELSE_NAME).unwrap().clone(), vec![condition, left, right]))
    })
}

fn parse_term<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
) -> Result<Formula, E> {
    match_or_err!(Rule::term, p; {
        let mut inner_rule = p.into_inner();
        let np = inner_rule.next().unwrap();
        match np.as_rule() {
            Rule::application => parse_application(ctx, np, memory),
            _ => unreachable!()
        }
    })
}

fn parse_cnf<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &HashMap<&'a str, Formula>,
) -> Result<CNF, E> {
    todo!()
}
