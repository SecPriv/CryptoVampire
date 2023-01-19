extern crate pest;
use crate::{
    formula::{env::Environement, function::FFlags, macros::fun},
    problem::{
        crypto_assumptions::CryptoAssumption,
        problem::{Problem, ProblemBuilder},
    },
    smt::macros::sfun,
};
use std::{borrow::Borrow, cell::Ref, collections::HashMap};

use crate::{
    formula::{
        builtins::{functions::*, types::*},
        formula::{RichFormula, Variable},
        function::Function,
        quantifier::Quantifier,
        sort::Sort,
    },
    problem::protocol::Step,
};

use itertools::{Either, Itertools};
use pest::{
    error::{Error, ErrorVariant},
    iterators::{Pair, Pairs},
    Parser, Span,
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

#[derive(Debug)]
struct Context<'a> {
    env: Environement,
    steps: HashMap<&'a str, Step>,
    assertions: Vec<RichFormula>,
    query: Option<RichFormula>,
    lemmas: Vec<RichFormula>,
    crypto_assumptions: Vec<CryptoAssumption>,
    order: Vec<RichFormula>,
    macros: HashMap<&'a str, Macro>,
}

#[derive(Debug)]
struct Macro {
    ids: Vec<usize>,
    sorts: Vec<Sort>,
    content: RichFormula,
}

impl<'a> Context<'a> {
    fn to_pb_builder(self) -> ProblemBuilder {
        let Context {
            env,
            steps,
            assertions,
            query,
            lemmas,
            crypto_assumptions,
            order,
            macros: _,
        } = self;
        ProblemBuilder {
            steps: steps.into_iter().map(|(_, t)| t).collect(),
            env,
            assertions,
            query: query.unwrap(),
            order,
            lemmas,
            crypto_assumptions,
        }
    }

    fn available_fun_name(&self, name: &str) -> bool {
        !(FORBIDDEN_NAMES.contains(&name)
            || self.env.get_f(name).is_some()
            || self.macros.contains_key(name))
    }

    fn available_sort_name(&self, name: &str) -> bool {
        !(FORBIDDEN_NAMES.contains(&name) || self.env.get_s(name).is_some())
    }
}

impl<'a> From<Environement> for Context<'a> {
    fn from(env: Environement) -> Self {
        Context {
            env,
            steps: Default::default(),
            assertions: Default::default(),
            query: Default::default(),
            lemmas: Default::default(),
            crypto_assumptions: Default::default(),
            order: Default::default(),
            macros: Default::default(),
        }
    }
}
const MSG_MACRO: &'static str = "msg";
const COND_MACRO: &'static str = "cond";
const FORBIDDEN_NAMES: &'static [&'static str] = &[
    "subterm", "ite", "=", "<", ">", "assert", "if", "then", "else", MSG_MACRO, COND_MACRO,
];

pub fn parse_protocol(env: Environement, str: &str) -> Result<Problem, E> {
    let mut ctx = env.into();

    let c = MainParser::parse(Rule::content, str)?.next().unwrap();
    // println!("{:?}", c);

    for p in c.into_inner() {
        let span = p.as_span();
        match p.as_rule() {
            Rule::EOI => (),
            Rule::declaration => parse_declaration(&mut ctx, p)?,
            Rule::step => {
                parse_step(&mut ctx, p)?;
            }
            Rule::assertion => {
                let mut memory = HashMap::new();
                let assert = parse_term_as(
                    &ctx,
                    p.into_inner().next().unwrap(),
                    &mut memory,
                    Some(BOOL(&ctx.env)),
                )?;

                if assert.iter().all(|f| match f {
                    RichFormula::Quantifier(Quantifier::FindSuchThat { variables: _ }, _) => false,
                    _ => true,
                }) {
                    ctx.assertions.push(assert)
                } else {
                    perr!(
                        span ;
                        "\"try find such that\" are not allowed in assertions",
                    )?;
                }
            }
            Rule::query => {
                if ctx.query.is_some() {
                    perr!(
                        span;
                        "can't define two queries, use lemmas to prove intermediary results",
                    )?;
                } else {
                    let mut memory = HashMap::new();
                    let query = parse_term_as(
                        &ctx,
                        p.into_inner().next().unwrap(),
                        &mut memory,
                        Some(BOOL(&ctx.env)),
                    )?;
                    if query.iter().all(|f| match f {
                        RichFormula::Quantifier(Quantifier::FindSuchThat { variables: _ }, _) => {
                            false
                        }
                        _ => true,
                    }) {
                        ctx.query = Some(query);
                    } else {
                        perr!(span; "\"try find such that\" are not allowed in query",)?;
                    }
                }
            }
            Rule::order => {
                let f = parse_order(&mut ctx, p)?;
                ctx.order.push(f)
            }
            Rule::lemma => {
                let mut memory = HashMap::new();
                let lemma = parse_term_as(
                    &ctx,
                    p.into_inner().next().unwrap(),
                    &mut memory,
                    Some(BOOL(&ctx.env)),
                )?;

                if lemma.iter().all(|f| match f {
                    RichFormula::Quantifier(Quantifier::FindSuchThat { variables: _ }, _) => false,
                    _ => true,
                }) {
                    ctx.lemmas.push(lemma)
                } else {
                    perr!(
                        span ;
                        "\"try find such that\" are not allowed in lemmas",
                    )?;
                }
            }
            Rule::assertion_crypto => {
                parse_crypto(&mut ctx, p)?;
            }
            Rule::mlet => {
                let (name, m) = parse_let(&mut ctx, p)?;
                ctx.macros.insert(name, m);
            }
            r => unreachable!("{:?}", r),
        }
    }
    let pbbuild = ctx.to_pb_builder();
    Ok(Problem::new(pbbuild))
}

fn span_err(s: Span, str: String) -> E {
    Error::new_from_span(ErrorVariant::CustomError { message: str }, s)
}

fn parse_crypto<'a>(ctx: &mut Context, p: Pair<'a, Rule>) -> Result<(), E> {
    let msg = MSG(&ctx.env);
    let bool = BOOL(&ctx.env);
    let p_span = p.as_span();
    let mut inner = p.into_inner();

    fn finished<'a>(mut inner: Pairs<'a, Rule>) -> Result<(), E> {
        if let Some(inner) = inner.next() {
            Err(span_err(
                inner.as_span(),
                format!("unexpected extra argument"),
            ))
        } else {
            Ok(())
        }
    }

    let ident = inner.next().unwrap();
    match ident.as_str() {
        // "euf-cma-hash" => {
        //     let hash_f_rule = inner.next().unwrap();
        //
        //     let hash_f = match ctx.env.get_f(hash_f_rule.as_str()) {
        //         Some(h) => h,
        //         _ => perr!(hash_f_rule.as_span(); "{} is not defined", hash_f_rule.as_str())?,
        //     };
        //     let mmsg = MSG(&ctx.env);
        //     if hash_f
        //         .get_input_sorts()
        //         .iter()
        //         .chain(std::iter::once(&hash_f.get_output_sort()))
        //         .all(|s| s == mmsg)
        //     {
        //         ctx.crypto_assumptions
        //             .push(CryptoAssumption::EufCmaMac { mac: hash_f.clone() });
        //         Ok(())
        //     } else {
        //         perr!( hash_f_rule.as_span();
        //                         "{} should have type {} -> {} -> {} as it should be a keyed hash",
        //                         hash_f_rule.as_str(), MSG(&ctx.env).name(), MSG(&ctx.env).name(), MSG(&ctx.env).name())
        //     }
        // }
        "nonce" => {
            ctx.crypto_assumptions.push(CryptoAssumption::Nonce);
            finished(inner)
        }
        "euf-cma" => {
            let sign = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'sign'")))?;
            let verify = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'verify'")))?;
            let pk = inner.next();

            let sort_vec: [&[&Sort]; 3] = [&[msg, msg, msg], &[bool, msg, msg, msg], &[msg, msg]];
            let tmp: Result<Vec<_>, _> = [&sign, &verify]
                .into_iter()
                .chain(pk.as_ref())
                .map(|r| {
                    let s = r.as_span();
                    (
                        s,
                        ctx.env
                            .get_f(r.as_str())
                            .ok_or(span_err(s, format!("no function {}", r.as_str()))),
                    )
                })
                .zip(sort_vec.into_iter())
                .map(|((span, f), s)| match f {
                    Ok(f) => {
                        let ss: Vec<_> = f.sort_iter().collect();
                        if s.len() == ss.len() && ss.iter().zip(s.iter()).all(|(ss, s)| ss.eq(s)) {
                            Ok(f)
                        } else {
                            let mut got = ss.iter();
                            let got_final = got.next().into_iter();
                            let got = got.chain(got_final).map(|s| s.name()).join(" -> ");

                            let mut expected = s.iter();
                            let expected_final = expected.next().into_iter();
                            let expected = expected.chain(expected_final).map(|s| s.name()).join(" -> ");

                            Err(span_err(
                                span,
                                format!(
                                    "{} doesn't have the right signature.\n\texpected: {}\n\tgot: {}\n\t function: {:?}",
                                    f.name(), expected, got, f
                                ),
                            ))
                        }
                    }
                    Err(e) => Err(e),
                })
                .collect();
            let tmp = tmp?;

            for f in tmp.iter() {
                if !f.is_user_defined() {
                    return Err(span_err(
                        p_span,
                        format!("{} is not user defined!", f.name()),
                    ));
                }
            }

            if pk.is_some() {
                debug_assert_eq!(tmp.len(), 3);
                ctx.crypto_assumptions.push(CryptoAssumption::EufCmaSign {
                    sign: tmp[0].clone(),
                    verify: tmp[1].clone(),
                    pk: tmp[2].clone(),
                });
            } else {
                debug_assert_eq!(tmp.len(), 2);
                ctx.crypto_assumptions.push(CryptoAssumption::EufCmaMac {
                    mac: tmp[0].clone(),
                    verify: tmp[1].clone(),
                })
            }
            finished(inner)
        }
        "int-ctxt" => {
            let enc = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'enc'")))?;
            let dec = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'dec'")))?;
            let verify = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'fail'")))?;
            let fail = inner
                .next()
                .ok_or(span_err(p_span, format!("expect a function for 'fail'")))?;

            let sort_vec: [&[&Sort]; 4] = [
                &[msg, msg, msg, msg],
                &[msg, msg, msg],
                &[bool, msg, msg],
                &[msg],
            ];
            let tmp: Result<Vec<_>, _> = [&enc, &dec, &verify, &fail]
                .into_iter()
                .map(|r| {
                    let s = r.as_span();
                    (
                        s,
                        ctx.env
                            .get_f(r.as_str())
                            .ok_or(span_err(s, format!("no function {}", r.as_str()))),
                    )
                })
                .zip(sort_vec.into_iter())
                .map(|((span, f), s)| match f {
                    Ok(f) => {
                        let ss: Vec<_> = f.sort_iter().collect();
                        if s.len() == ss.len() && ss.iter().zip(s.iter()).all(|(ss, s)| ss.eq(s)) {
                            Ok(f)
                        } else {
                            let signature_exp = s.iter().map(|s| s.name()).join(" -> ");
                            let signature_got = ss.iter().map(|s| s.name()).join(" -> ");
                            Err(span_err(
                                span,
                                format!(
                                    "doessn't have the right signature\n\tgot: {}\n\texpected: {}",
                                    signature_got, signature_exp
                                ),
                            ))
                        }
                    }
                    Err(e) => Err(e),
                })
                .collect();
            let tmp = tmp?;

            ctx.crypto_assumptions.push(CryptoAssumption::IntCtxtSenc {
                enc: tmp[0].clone(),
                dec: tmp[1].clone(),
                fail: tmp[3].clone(),
                verify: tmp[2].clone(),
            });
            finished(inner)
        }
        s => perr!(ident.as_span(); "{} is not a valid crypto assumption", s),
    }
}

fn parse_let<'a>(ctx: &mut Context, p: Pair<'a, Rule>) -> Result<(&'a str, Macro), E> {
    let mut inner = p.into_inner();
    let name = inner.next().unwrap();
    let args = inner.next().unwrap();
    let content = inner.next().unwrap();

    let name = if !ctx.available_fun_name(name.as_str()) {
        perr!(name.as_span(); "{} is already taken", name.as_str())
    } else {
        Ok(name.as_str())
    }?;
    let mut memory = Default::default();
    let (ids, sorts) = parse_typed_arguments(ctx, args, &mut memory)?
        .into_iter()
        .map(|(_, Variable { id, sort })| (id, sort))
        .unzip();
    let content = parse_term_as(ctx, content, &mut memory, None)?;

    Ok((
        name,
        Macro {
            ids,
            sorts,
            content,
        },
    ))
}

fn parse_type(ctx: &Context, p: Pair<Rule>) -> Result<Sort, E> {
    match_or_err!(Rule::type_name, p; {
        match ctx.env.get_s(p.as_str()) {
            Some(f) => Ok(f.clone()),
            _ => uerr!(p, "type"),
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
                if !ctx.available_fun_name(var.as_str()) {
                    perr!(var, "the name '{}' is used for both a variable and a function or is forbidden", var.as_str())
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
        // if ctx.env.get_sorts().contains_key(t){
        //     rerr!(inner, "type")
        // } else {
        //     ctx.env.add_s(t.into());
        //     Ok(())
        // }
        // match ctx.env.add_s(t.into()) {
        //     true => Ok(()),
        //     _ => rerr!(inner, "type")
        // }

        if ctx.available_sort_name(t) {
            ctx.env.add_s(t.into());
            Ok(())
        } else {
            rerr!(inner, "type")
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

        // match ctx.env.get_f(name) {
        //     None => {
                let flags = FFlags::USER_DEFINED |
                    // if input_sorts
                    //     .iter()
                    //     .chain(std::iter::once(&output_sort))
                    //     .find(|s| (s.name() == MSG_NAME) || (s.name() == CONDITION_NAME))
                    //     .is_some()
                    if output_sort.is_term_algebra() || &output_sort == BOOL(&ctx.env)
                    {
                        FFlags::TERM_ALGEBRA
                    } else {
                        FFlags::empty()
                    };
                let f = Function::new_with_flag(name, input_sorts, output_sort, flags);
                // match ctx.env.add_f(f) {
                //     true => Ok(()),
                //     _ => perr!(name_rule, "redeclaring function: {}", name)
                // }
                if ctx.available_fun_name(f.name()) {
                    ctx.env.add_f(f);
                    Ok(())
                } else {
                    perr!(name_rule, "redeclaring function: {} (or forbidden)", name)
                }
            // },
            // _ => perr!(name_rule, "redeclaring function: {}", name)
        // }
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
        let formula = match memory.get(name.as_str()) {
            Some(var) => {
                if inner_rule.next().is_none() {
                    Ok(RichFormula::Var(var.clone()))
                } else {
                    perr!(span; "a varibale is not a function",)
                }
            }
            _ if name.as_str() == MSG_MACRO || name.as_str() == COND_MACRO => {
                let stp  = inner_rule.next().ok_or(
                    Error::new_from_span(
                        ErrorVariant::CustomError {
                            message: format!("should be an application"),
                        },
                        name.as_span())
                    )?;
                let stp_span = stp.as_span();
                let stp = parse_term_as(ctx, stp, memory, Some(&STEP(&ctx.env).clone()))?;
                let (stp_f, args) = match &stp {
                    RichFormula::Fun(f, args) => Ok((f, args)),
                    _ => perr!(stp_span; "expected application" ,)
                }?;

                let stp_p = ctx.steps.get(stp_f.name()).ok_or(
                    Error::new_from_span(
                        ErrorVariant::CustomError {
                            message: format!("unknown step {}", stp_f.name()),
                        },
                        stp_span)
                    )?;

                if name.as_str() == MSG_MACRO {
                    Ok(stp_p.apply_message(args))
                } else { // name.as_str() == COND_MACRO
                    Ok(stp_p.apply_condition(args))

                }
            }
            _ => {
                let (fun, sorts) = match ctx.env.get_f(name.as_str()) {
                    None => {
                        if let Some(m) = ctx.macros.get(name.as_str()) {
                            (Either::Right(m), m.sorts.clone())
                        } else {
                            let nxt = inner_rule.next();
                            if nxt.is_none() {
                                return uerr!(name, "constant or variable")
                            } else {
                                return uerr!(name, "function")
                            }
                        }
                    }
                    Some(fun) => {
                        (Either::Left(fun), fun.get_input_sorts().clone())
                    }
                };
                let mut i = 0;

                let args: Result<Vec<_>,_> = sorts.iter().map(|s|{
                    match inner_rule.next() {
                        None => {
                            // dbg!(&fun);
                            perr!(span; "not enough arguments, expected {} got {}", sorts.len(), i)
                        },
                        Some(arg) => {
                            i += 1;
                            parse_term_as(ctx, arg, memory, Some(s))
                        }
                    }
                }).collect();
                let args = args?;

                if inner_rule.next().is_some() {
                    return perr!(span; "too many arguments, expected {} got {}", sorts.len(), i)
                }

                let formula = match fun{
                    Either::Left(fun) => RichFormula::Fun(fun.clone(), args),
                    Either::Right(m) => m.content.clone().apply_substitution(&m.ids, args.as_slice()),
                };
                Ok(formula)

            }
        }?;

        // sugar for nonces
        if &formula.get_sort(&ctx.env) == NONCE(&ctx.env) {
            Ok(RichFormula::Fun(NONCE_MSG(&ctx.env).clone(), vec![formula]))
        } else {
            Ok(formula)
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
        if mtype.is_none() || Some(&r.get_sort(&ctx.env)) == mtype {
            Ok(r)
        } else {
            perr!(span; "wrong type, expected {} got {}", mtype.unwrap(), r.get_sort(&ctx.env))
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

        let condition = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(BOOL(&ctx.env)))?;
        let left = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(MSG(&ctx.env)))?;
        let right = parse_term_as(ctx, inner_rule.next().unwrap(), memory, Some(MSG(&ctx.env)))?;

        let condition = condition.into();

        Ok(fun!(IF_THEN_ELSE(&ctx.env); condition, left, right))
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
            Rule::hard_eq => todo!(),
            Rule::eq | Rule::neq => parse_term_as(ctx, lhs,
                memory, Some(MSG(&ctx.env)))?,
            _ => parse_term_as(ctx, lhs,
                memory, Some(BOOL(&ctx.env)))?,
        };
        while let Some(mop) = op {
            let rhs = inner.next().unwrap();
            let end = rhs.as_span().end_pos();

            lhs_formula = match mop.as_rule() {
                Rule::hard_eq => todo!(),
                Rule::eq => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(MSG(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == MSG(&ctx.env) {
                        Ok(fun!(EQUALITY(&ctx.env); lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            MSG(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                Rule::neq => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(MSG(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == MSG(&ctx.env) {
                        Ok(not(&ctx.env, fun!(EQUALITY(&ctx.env); lhs_formula, rhs_formula)))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            MSG(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                Rule::or => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(BOOL(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == BOOL(&ctx.env) {
                        Ok(f_or(&ctx.env, lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            BOOL(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                Rule::and => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(BOOL(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == BOOL(&ctx.env) {
                        Ok(f_and(&ctx.env, lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            BOOL(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                Rule::implies => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(BOOL(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == BOOL(&ctx.env) {
                        Ok(implies(&ctx.env, lhs_formula, rhs_formula))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            BOOL(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                Rule::iff => {
                    let rhs_formula = parse_term_as(ctx, rhs,
                        memory, Some(BOOL(&ctx.env)))?;
                    if &lhs_formula.get_sort(&ctx.env) == BOOL(&ctx.env) {
                        Ok(f_and(&ctx.env,
                            implies(&ctx.env, lhs_formula.clone(), rhs_formula.clone()),
                            implies(&ctx.env, rhs_formula, lhs_formula),
                        ))
                    } else {
                        perr!(
                            lhs_span; "wrong type, expected {} got {}",
                            BOOL(&ctx.env), lhs_formula.get_sort(&ctx.env))
                    }
                }
                _ => unreachable!()
            }?;
            lhs_span = lhs_span.start_pos().span(&end);
            op = inner.next();
        }
        if mtype.is_none() || Some(&lhs_formula.get_sort(&ctx.env)) == mtype {
            Ok(lhs_formula)
        } else {
            perr!(lhs_span; "wrong type, expected {} got {}",
                mtype.unwrap(), lhs_formula.get_sort(&ctx.env))
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
        let content = parse_term_as(ctx, inner.next().unwrap(), memory, Some(BOOL(&ctx.env)))?;

        let (strs, vars) :(Vec<_>, Vec<_>) = to_be_freed.into_iter().unzip();

        let r = RichFormula::Quantifier( {match op.as_rule(){
            Rule::forall =>  Quantifier::Forall { variables: vars },
            Rule::exists =>  Quantifier::Exists { variables: vars },
            _ => unreachable!()
        }}, vec![content] );

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
        let cond = parse_term_as(ctx, inner.next().unwrap(), memory, Some(BOOL(&ctx.env)))?;
        let ml = parse_term_as(ctx, inner.next().unwrap(), memory, Some(MSG(&ctx.env)))?;
        let mr = parse_term_as(ctx, inner.next().unwrap(), memory, Some(MSG(&ctx.env)))?;

        let r = RichFormula::Quantifier(Quantifier::FindSuchThat { variables: vars },vec![cond, ml, mr]);
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
        memory.insert("in", Variable::new(0, MSG(&ctx.env).clone()));

        let name = inner.next().unwrap().as_str();
        if ctx.steps.contains_key(name) || ctx.env.contain_key_f(name) || FORBIDDEN_NAMES.contains(&name) {
            return perr!(span ; "the name {} is already taken", name);
        }


        let (_to_be_freed, sorts, vars): (Vec<_>, Vec<_>, Vec<_>) =
            parse_typed_arguments(ctx, inner.next().unwrap(), &mut memory)?.into_iter().map(|(s,v)| (s,v.sort.clone(),v)).multiunzip();

        let f = Function::new_step(&ctx.env, name, &sorts);
        ctx.env.add_f(f.clone());

        let cond = parse_term_as(ctx, inner.next().unwrap(), &mut memory, Some(BOOL(&ctx.env)))?;
        let msg = parse_term_as(ctx, inner.next().unwrap(), &mut memory, Some(MSG(&ctx.env)))?;

        let r = Step::new(name, vars, cond, msg, f);
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

        let step = STEP(&ctx.env);
        let happens = HAPPENS(&ctx.env);

        let mut memory = HashMap::new();
        let variables = parse_typed_arguments(ctx, args, &mut memory)?
            .into_iter().map(|(_, v)| v).collect();

        let stp1 = parse_term_as(ctx, stp1, &mut memory, Some(step))?;
        let stp2 = parse_term_as(ctx, stp2, &mut memory, Some(step))?;

        let formula = match op.as_str() {
            "<" => fun!(LT(&ctx.env); stp1, stp2),
            ">" => fun!(LT(&ctx.env); stp2, stp1),
            "<>" => implies(
                &ctx.env,
                f_and(&ctx.env, fun!(happens; stp1.clone()), fun!(happens; stp2.clone())),
                fun!(EQUALITY(&ctx.env); stp1, stp2)
            ),
            _ => unreachable!()
        };

        Ok(RichFormula::Quantifier({match quantifier_op.as_rule() {
            Rule::forall => Quantifier::Forall { variables },
            Rule::exists => Quantifier::Exists { variables },
            _ => unreachable!()
        }}, vec![formula]))
    })
}
