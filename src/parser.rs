extern crate pest;
use std::collections::HashMap;

use crate::{
    formula::{
        builtins::{functions::*, types::*},
        formula::{fun, quant, Formula, Variable, CNF},
        function::Function,
        quantifier::Quantifier,
        sort::Sort,
    },
    problem::protocol::{Protocol, Step},
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
    steps: HashMap<&'a str, Step>,
}
impl<'a> Context<'a> {
    fn to_protocol(self) -> Protocol {
        let Context { types, funs, steps } = self;
        Protocol::new(
            steps.into_iter().map(|(_k, v)| v),
            funs.into_iter().map(|(_k, v)| v),
            types.into_iter().map(|(_k, v)| v),
        )
    }
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
            (STEP_NAME, STEP.clone()),
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
            (EQUALITY_NAME, EQUALITY.clone()),
            (INPUT_NAME, INPUT.clone()),
            (FAIL_NAME, FAIL.clone()),
        ]
        .into_iter(),
    );

    let c = MainParser::parse(Rule::content, str)?.next().unwrap();
    // println!("{:?}", c);

    for p in c.into_inner() {
        match p.as_rule() {
            Rule::EOI => (),
            Rule::declaration => parse_declaration(&mut ctx, p)?,
            Rule::step => {
                parse_step(&mut ctx, p)?;
            }
            Rule::assertion => {
                let mut memory = HashMap::new();
                parse_cnf(&ctx, p.into_inner().next().unwrap(), &mut memory)?;
            }
            Rule::query => {
                let mut memory = HashMap::new();
                parse_cnf(&ctx, p.into_inner().next().unwrap(), &mut memory)?;
            }
            Rule::order => (),
            r => unreachable!("{:?}", r),
        }
    }
    Ok(ctx.to_protocol())
}

fn parse_type(ctx: &Context, p: Pair<Rule>) -> Result<Sort, E> {
    match_or_err!(Rule::type_name, p; {
        match ctx.types.get(p.as_str()) {
            Some(f) => Ok(f.clone()),
            _ => {
                uerr!(p, "type")}
        }
    })
}

fn parse_variable_binding<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<(&'a str, Variable), E> {
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

        let var_f = Variable::new(memory.len(), var_type);
        memory.insert(var, var_f.clone());
        Ok((var, var_f))
    })
}

fn parse_declare_function_args<'a>(ctx: &Context<'a>, p: Pair<'a, Rule>) -> Result<Vec<Sort>, E> {
    match_or_err!(Rule::declare_function_args, p; {
        let inner_rule = p.into_inner();
        inner_rule.map(|p2| parse_type(ctx, p2)).collect()
    })
}

fn parse_declare_type<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<(), E> {
    match_or_err!(Rule::declare_type, p; {
        let inner = p.into_inner().next().unwrap();
        let t = inner.as_str();
        if ctx.types.contains_key(t){
            rerr!(inner, "type")
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
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::application, p; {
        let span = p.as_span();

        let mut inner_rule = p.into_inner();

        let name = inner_rule.next().unwrap(); // can't fail
        match memory.get(name.as_str()) {
            Some(var) => {
                if inner_rule.next().is_none() {
                    Ok(Formula::Var(var.clone()))
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
    memory: &mut HashMap<&'a str, Variable>,
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
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::if_then_else, p; {
        let mut inner_rule = p.into_inner();

        let condition = parse_cnf(ctx, inner_rule.next().unwrap(), memory)?;
        let left = parse_term_as_type(ctx, inner_rule.next().unwrap(), memory, &MSG)?;
        let right = parse_term_as_type(ctx, inner_rule.next().unwrap(), memory, &MSG)?;

        let condition = condition.into();

        Ok(fun!(ctx.funs.get(IF_THEN_ELSE_NAME).unwrap(); condition, left, right))
    })
}

fn parse_term<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::term, p; {
        let mut inner_rule = p.into_inner();
        let np = inner_rule.next().unwrap();
        match np.as_rule() {
            Rule::application => parse_application(ctx, np, memory),
            Rule::if_then_else => parse_if_then_else(ctx, np, memory),
            Rule::find_such_that => parse_find_such_that(ctx, np, memory),
            _ => unreachable!()
        }
    })
}

fn parse_cnf<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<CNF, E> {
    match_or_err!(Rule::cnf, p; {
        let inner = p.into_inner();
        let clauses : Result<Vec<_>, E> =  inner.map(|r| parse_disjonction(ctx, r, memory)).collect();
        Ok(CNF::new(clauses?))
    })
}

fn parse_disjonction<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Vec<Formula>, E> {
    match_or_err!(Rule::disjunction, p; {
        p.into_inner().map(|r| parse_bool(ctx, r, memory)).collect()
    })
}

fn parse_bool<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::bool, p; {
        let inner = p.into_inner().next().unwrap();
        match inner.as_rule() {
            Rule::term => parse_term(ctx, inner, memory),
            Rule::infix_term => parse_infix_term(ctx, inner, memory),
            Rule::quantifier => parse_quantifier(ctx, inner, memory),
            _ => unreachable!()
        }
    })
}

fn parse_infix_term<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::infix_term, p; {
        let mut inner = p.into_inner();
        let tl = inner.next().unwrap();
        let op = inner.next().unwrap();
        let tr = inner.next().unwrap();

        match op.as_str() {
            "==" => Ok(fun!(EQUALITY;
                    parse_term_as_type(ctx, tl, memory, &MSG)?,
                    parse_term_as_type(ctx, tr, memory, &MSG)?)),
            "!=" => Ok(not(fun!(EQUALITY;
                    parse_term_as_type(ctx, tl, memory, &MSG)?,
                    parse_term_as_type(ctx, tr, memory, &MSG)?))),
            s => perr!(op.as_span(); "{} is not a valid operator", s)

        }
    })
}

fn parse_typed_arguments<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Vec<(&'a str, Variable)>, E> {
    match_or_err!(Rule::typed_arguments, p;{
        let inner = p.into_inner();
        inner.map(|vb| parse_variable_binding(ctx, vb, memory)).collect()
    })
}

fn parse_quantifier<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::quantifier, p; {
        let mut inner = p.into_inner();

        let op = inner.next().unwrap();
        let to_be_freed =  parse_typed_arguments(ctx, inner.next().unwrap(), memory)?;
        let content = parse_cnf(ctx, inner.next().unwrap(), memory)?.into();

        let (strs, vars) :(Vec<_>, Vec<_>) = to_be_freed.into_iter().unzip();

        let r = quant!( {match op.as_rule(){
            Rule::forall =>  Quantifier::Forall { variable: vars },
            Rule::exists =>  Quantifier::Exists { variable: vars },
            _ => unreachable!()
        }}; content );

        for s in strs{
            memory.remove(s).unwrap();
        }

        Ok(r)
    })
}

fn parse_find_such_that<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<Formula, E> {
    match_or_err!(Rule::find_such_that, p;{
        let mut inner = p.into_inner();
        let (to_be_freed, vars): (Vec<_>, Vec<_>) =
            parse_typed_arguments(ctx, inner.next().unwrap(), memory)?.into_iter().unzip();
        let cond = parse_cnf(ctx, inner.next().unwrap(), memory)?.into();
        let ml = parse_term_as_type(ctx, inner.next().unwrap(), memory, &MSG)?;
        let mr = parse_term_as_type(ctx, inner.next().unwrap(), memory, &MSG)?;

        let r = quant!(Quantifier::FindSuchThat { variable: vars }; cond, ml, mr);
        to_be_freed.iter().for_each(|s| {memory.remove(s).unwrap();});
        Ok(r)
    })
}

fn parse_declaration<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<(), E> {
    match_or_err!(Rule::declaration, p; {
        let d = p.into_inner().next().unwrap();
        match d.as_rule() {
            Rule::declare_type => parse_declare_type(ctx, d),
            Rule::declare_function => parse_declare_function(ctx, d),
            _ => unreachable!()
        }
    })
}

fn parse_step<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<Step, E> {
    match_or_err!(Rule::step, p;{
        let span = p.as_span();
        let mut inner = p.into_inner();

        let mut memory = HashMap::new();
        memory.insert("in", Variable::new(0, MSG.clone()));

        let name = inner.next().unwrap().as_str();
        if ctx.steps.contains_key(name) || ctx.funs.contains_key(name) || FORBIDDEN_NAMES.contains(&name) {
            return perr!(span ; "the name {} is already taken", name);
        }


        let (_to_be_freed, sorts): (Vec<_>, Vec<_>) =
            parse_typed_arguments(ctx, inner.next().unwrap(), &mut memory)?.into_iter().map(|(s,v)| (s,v.sort)).unzip();

        let f = Function::new_from_step(
            name,
            sorts.clone(),
            STEP.clone());
        ctx.funs.insert(name, f);

        let cond = parse_cnf(ctx, inner.next().unwrap(), &mut memory)?;
        let msg = parse_term_as_type(ctx, inner.next().unwrap(), &mut memory, &MSG)?;

        let r = Step::new(name, sorts, cond, msg);
        // to_be_freed.iter().for_each(|s| {memory.remove(s).unwrap();});
        ctx.steps.insert(name, r.clone());
        Ok(r)

    })
}
