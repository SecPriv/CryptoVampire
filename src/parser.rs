extern crate pest;
use std::collections::HashMap;

use crate::{
    formula::{
        builtins::{functions::*, types::*},
        formula::{fun, quant, RichFormula, Variable, CNF},
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
    assertions: Vec<RichFormula>,
    query: Option<RichFormula>,
    lemma: Vec<RichFormula>,
    order: Vec<RichFormula>,
}
impl<'a> Context<'a> {
    fn to_protocol(self) -> Protocol {
        let Context { 
            types, 
            funs, 
            steps,
            assertions,
            query,
            lemma,
            order
        } = self;
        Protocol::new(steps.into_iter().map(|(_k, v)| v))
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
            (LT_NAME, LT.clone()),
            (HAPPENS_NAME, HAPPENS.clone())
        ]
        .into_iter(),
    );

    let c = MainParser::parse(Rule::content, str)?
            .next().unwrap();
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
                let assert = parse_term_as(
                    &ctx, p.into_inner().next().unwrap(), 
                    &mut memory, Some(&BOOL))?;
                ctx.assertions.push(assert)
            }
            Rule::query => {
                if ctx.query.is_some() {
                    perr!(p, "can't define two queries, use lemmas to prove intermediary results".to_owned())?;
                } else {
                    let mut memory = HashMap::new();
                    let query = parse_term_as(
                        &ctx, p.into_inner().next().unwrap(), 
                        &mut memory, Some(&BOOL))?;
                    ctx.query = Some(query);
                }
            }
            Rule::order => {
                let f = parse_order(&mut ctx, p)?;
                ctx.order.push(f)
            }
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
) -> Result<RichFormula, E> {
    match_or_err!(Rule::application, p; {
        let span = p.as_span();

        let mut inner_rule = p.into_inner();

        let name = inner_rule.next().unwrap(); // can't fail
        match memory.get(name.as_str()) {
            Some(var) => {
                if inner_rule.next().is_none() {
                    Ok(RichFormula::Var(var.clone()))
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
                            parse_term_as(ctx, arg, memory, Some(s))
                        }
                    }
                }).collect();
                let args = args?;

                if inner_rule.next().is_some() {
                    perr!(span; "too many arguments, expected {} got {}", fun.arity(), i)
                } else {
                    let formula = RichFormula::Fun(fun.clone(), args);
                    if formula.get_sort() == &NONCE.clone() {
                        Ok(RichFormula::Fun(NONCE_MSG.clone(), vec![formula]))
                    } else {
                        Ok(formula)
                    }
                }
            }
        }
    })
}

fn parse_term_as<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
    mtype: Option<&Sort>,
) -> Result<RichFormula, E> {
    match_or_err!(Rule::term, p; {
        let inner = p.into_inner().next().unwrap();
        parse_inner_term_as(ctx, inner, memory, mtype)
    })
}

fn parse_commun_base<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<RichFormula, E> {
    match_or_err!(Rule::commun_base, p ; {
        let np = p.into_inner().next().unwrap();
        match np.as_rule() {
            Rule::application => parse_application(ctx, np, memory),
            Rule::if_then_else => parse_if_then_else(ctx, np, memory),
            Rule::find_such_that => parse_find_such_that(ctx, np, memory),
            Rule::quantifier => parse_quantifier(ctx, np, memory),
            _ => unreachable!(),
        }
    })
}

fn parse_inner_term_as<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
    mtype: Option<&Sort>,
) -> Result<RichFormula, E> {
    match_or_err!(Rule::inner_term, p; {
        let span = p.as_span();
        let mut inner_rule = p.into_inner();
        let np = inner_rule.next().unwrap();
        let r = match np.as_rule() {
            Rule::infix_term => parse_infix_term_as(ctx, np, memory, None),
            _ => parse_commun_base(ctx, np, memory),
        }?;
        if mtype.is_none() || Some(r.get_sort()) == mtype {
            Ok(r)
        } else {
            perr!(span; "wrong type, expected {} got {}", mtype.unwrap(), r.get_sort())
        }
    })
}

fn parse_if_then_else<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
) -> Result<RichFormula, E> {
    match_or_err!(Rule::if_then_else, p; {
        let mut inner_rule = p.into_inner();

        let condition = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(&BOOL))?;
        let left = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(&MSG))?;
        let right = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(&MSG))?;

        let condition = condition.into();

        Ok(fun!(ctx.funs.get(IF_THEN_ELSE_NAME).unwrap(); condition, left, right))
    })
}

fn parse_infix_term_as<'a>(
    ctx: &Context<'a>,
    p: Pair<'a, Rule>,
    memory: &mut HashMap<&'a str, Variable>,
    mtype: Option<&Sort>,
) -> Result<RichFormula, E> {
    match_or_err!(Rule::infix_term, p; {
        let mut inner = p.into_inner();
        let lhs = inner.next().unwrap();
        let mut op = inner.next();

        let mut lhs_span = lhs.as_span();

        let mut lhs_formula = match op.as_ref().unwrap().as_rule() {
            Rule::eq | Rule::neq => parse_term_as(ctx, lhs, 
                memory, Some(&MSG))?,
            Rule::or | Rule::and => parse_term_as(ctx, lhs, 
                memory, Some(&BOOL))?,
            _ => unreachable!()
        };
        while let Some(mop) = op {
            let rhs = inner.next().unwrap();
            let end = rhs.as_span().end_pos();

            lhs_formula = match mop.as_rule() {
                Rule::eq => {
                    let rhs_formula = parse_term_as(ctx, rhs, 
                        memory, Some(&MSG))?;
                    if lhs_formula.get_sort() == &MSG.clone() {
                        Ok(fun!(EQUALITY; lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}", 
                            &MSG.clone(), lhs_formula.get_sort())
                    }
                }
                Rule::neq => {
                    let rhs_formula = parse_term_as(ctx, rhs, 
                        memory, Some(&MSG))?;
                    if lhs_formula.get_sort() == &MSG.clone() {
                        Ok(not(fun!(EQUALITY; lhs_formula, rhs_formula)))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}", 
                            &MSG.clone(), lhs_formula.get_sort())
                    }
                }
                Rule::or => {
                    let rhs_formula = parse_term_as(ctx, rhs, 
                        memory, Some(&BOOL))?;
                    if lhs_formula.get_sort() == &BOOL.clone() {
                        Ok(f_or(lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}", 
                            &BOOL.clone(), lhs_formula.get_sort())
                    }
                }
                Rule::and => {
                    let rhs_formula = parse_term_as(ctx, rhs, 
                        memory, Some(&BOOL))?;
                    if lhs_formula.get_sort() == &BOOL.clone() {
                        Ok(f_and(lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}", 
                            &BOOL.clone(), lhs_formula.get_sort())
                    }
                }
                _ => unreachable!()
            }?;
            lhs_span = lhs_span.start_pos().span(&end);
            op = inner.next();
        }
        if mtype.is_none() || Some(lhs_formula.get_sort()) == mtype {
            Ok(lhs_formula)
        } else {
            perr!(lhs_span; "wrong type, expected {} got {}", 
                mtype.unwrap(), lhs_formula.get_sort())
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
) -> Result<RichFormula, E> {
    match_or_err!(Rule::quantifier, p; {
        let mut inner = p.into_inner();

        let op = inner.next().unwrap();
        let to_be_freed =  parse_typed_arguments(ctx, inner.next().unwrap(), memory)?;
        let content = parse_term_as(ctx, inner.next().unwrap(), memory, Some(&BOOL))?;

        let (strs, vars) :(Vec<_>, Vec<_>) = to_be_freed.into_iter().unzip();

        let r = quant!( {match op.as_rule(){
            Rule::forall =>  Quantifier::Forall { variables: vars },
            Rule::exists =>  Quantifier::Exists { variables: vars },
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
) -> Result<RichFormula, E> {
    match_or_err!(Rule::find_such_that, p;{
        let mut inner = p.into_inner();
        let (to_be_freed, vars): (Vec<_>, Vec<_>) =
            parse_typed_arguments(ctx, inner.next().unwrap(), memory)?.into_iter().unzip();
        let cond = parse_term_as(ctx, inner.next().unwrap(), memory, Some(&BOOL))?;
        let ml = parse_term_as(ctx, inner.next().unwrap(), memory, Some(&MSG))?;
        let mr = parse_term_as(ctx, inner.next().unwrap(), memory, Some(&MSG))?;

        let r = quant!(Quantifier::FindSuchThat { variables: vars }; cond, ml, mr);
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

        let cond = parse_term_as(ctx, inner.next().unwrap(), &mut memory, Some(&BOOL))?;
        let msg = parse_term_as(ctx, inner.next().unwrap(), &mut memory, Some(&MSG))?;

        let r = Step::new(name, sorts, cond, msg);
        // to_be_freed.iter().for_each(|s| {memory.remove(s).unwrap();});
        ctx.steps.insert(name, r.clone());
        Ok(r)

    })
}

fn parse_order<'a>(ctx: &mut Context<'a>, p: Pair<'a, Rule>) -> Result<RichFormula, E> {
    match_or_err!(Rule::order, p; {
        let mut inner = p.into_inner();
        let quantifier_op = inner.next().unwrap();
        let args = inner.next().unwrap();
        let stp1 = inner.next().unwrap();
        let op = inner.next().unwrap();
        let stp2 = inner.next().unwrap();
        let _ = inner; // drop inner

        let mut memory = HashMap::new();
        let variables = parse_typed_arguments(ctx, args, &mut memory)?
            .into_iter().map(|(_, v)| v).collect();

        let stp1 = parse_term_as(ctx, stp1, &mut memory, Some(&STEP))?;
        let stp2 = parse_term_as(ctx, stp2, &mut memory, Some(&STEP))?;

        let formula = match op.as_str() {
            "<" => fun!(LT; stp1, stp2),
            ">" => fun!(LT; stp2, stp1),
            "<>" => not(f_and(fun!(HAPPENS; stp1), fun!(HAPPENS; stp2))),
            _ => unreachable!()
        };

        Ok(quant!({match quantifier_op.as_rule() {
            Rule::forall => Quantifier::Forall { variables },
            Rule::exists => Quantifier::Exists { variables },
            _ => unreachable!()
        }}; formula))
    })
}