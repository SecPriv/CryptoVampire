use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::IF_THEN_ELSE_NAME,
            types::{BITSTRING, BOOL, CONDITION, MSG},
        },
        env::Environement,
        formula::{RichFormula, Variable, sorts_to_variables},
        function::{FFlags, Function},
        sort::Sort,
        utils::Evaluator,
    },
    problem::problem::{
        CAND_NAME, CEQ_NAME, CFALSE_NAME, CNOT_NAME, COR_NAME, CTRUE_NAME, QuantifierPContent,
    },
    smt::{
        macros::*,
        smt::{RewriteKind, Smt, SmtFormula},
    },
};

use super::Ctx;

pub(crate) fn evaluate(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    // if !env.no_bitstring_fun() {
    if env.use_rewrite() {
        evaluate_rewrite(env, assertions, declarations, ctx)
    } else {
        let mut masserts = Vec::new();
        evaluate_rewrite(env, &mut masserts, declarations, ctx);
        assertions.extend(masserts.into_iter().map(|a| a.rewrite_to_assert(env)))
    }

    if env.legacy_evaluate() {
        legacy_evaluate(env, assertions, declarations, ctx)
    }
    // }

    user_evaluate(env, assertions, declarations, ctx)
}

fn legacy_evaluate(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    let msg = MSG(env);
    let cond = CONDITION(env);
    // let bitstring = BITSTRING(env);
    // let bool = BOOL(env);
    // let functions = &ctx.pbl.functions;
    // let evaluate_msg = get_eval_msg(ctx.env());
    // let evaluate_cond = get_eval_cond(ctx.env());
    let evaluate = Evaluator::new(ctx.env()).unwrap();

    let to_eval = |v: &Variable| {
        if &v.sort == cond {
            // sfun!(evaluate_cond; svar!(v.clone()))
            evaluate.cond(ctx, svar!(v.clone()))
        } else if &v.sort == msg {
            // sfun!(evaluate_msg; svar!(v.clone()))
            evaluate.msg(ctx, svar!(v.clone()))
        } else {
            svar!(v.clone())
        }
    };

    #[derive(Clone)]
    enum IsEval {
        Eval(Variable, Variable),
        NoEval(Variable),
    }

    fn filter_eval(e: &IsEval) -> Option<(&Variable, &Variable)> {
        match e {
            IsEval::Eval(v1, v2) => Some((v1, v2)),
            _ => None,
        }
    }

    fn to_tuple(e: IsEval) -> (Variable, Variable) {
        match e {
            IsEval::Eval(v1, v2) => (v1, v2),
            IsEval::NoEval(v) => (v.clone(), v),
        }
    }

    fn iter(e: IsEval) -> impl Iterator<Item = Variable> {
        match e {
            IsEval::Eval(v1, v2) => vec![v1, v2].into_iter(),
            IsEval::NoEval(v) => vec![v].into_iter(),
        }
    }

    assertions.extend(
        ctx.ta_funs
            .iter()
            .filter(|f| f.get_output_sort().is_evaluatable())
            .map(|f| {
                let vars_couple = f
                    .get_input_sorts()
                    .iter()
                    .enumerate()
                    .map(|(i, s)| {
                        if s.is_evaluatable() {
                            IsEval::Eval(
                                Variable {
                                    id: i * 2,
                                    sort: s.clone(),
                                },
                                Variable {
                                    id: i * 2 + 1,
                                    sort: s.clone(),
                                },
                            )
                        } else {
                            let v = Variable {
                                id: 2 * i,
                                sort: s.clone(),
                            };
                            IsEval::NoEval(v)
                        }
                    })
                    .collect_vec();

                let ands = vars_couple
                    .iter()
                    .filter_map(filter_eval)
                    .map(|(v1, v2)| seq!(to_eval(v1), to_eval(v2)))
                    .collect_vec();

                let (lvars, rvars): (Vec<_>, Vec<_>) = vars_couple
                    .iter()
                    .cloned()
                    .map(to_tuple)
                    .map(|(v1, v2)| (svar!(v1), svar!(v2)))
                    .unzip();

                SmtFormula::Forall(
                    vars_couple.into_iter().flat_map(iter).collect(),
                    Box::new({
                        let os = f.get_output_sort();
                        // let eval: Box<dyn Fn(SmtFormula) -> SmtFormula> = if &os == msg {
                        //     Box::new(evaluate_msg.clone())
                        // } else if &os == cond {
                        //     Box::new(evaluate_cond.clone())
                        // } else {
                        //     unreachable!()
                        // };
                        let eval = |f| {
                            if &os == msg {
                                evaluate.msg(ctx, f)
                            } else if &os == cond {
                                evaluate.cond(ctx, f)
                            } else {
                                unreachable!()
                            }
                        };

                        simplies!(env;
                            SmtFormula::And(ands),
                            seq!(
                                eval(sfun!(f, lvars)),
                                eval(sfun!(f, rvars))
                            )
                        )
                    }),
                )
            })
            .map(|f| Smt::Assert(f)),
    )
}
fn evaluate_rewrite(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    let msg = MSG(env);
    let cond = CONDITION(env);
    let bitstring = BITSTRING(env);
    let bool = BOOL(env);

    let rewriteb = Function::new(
        "r$rewriteb",
        vec![bitstring.clone(), bitstring.clone()],
        bool.clone(),
    );
    // let functions = &ctx.pbl.functions;
    // let evaluate_msg = get_eval_msg(ctx.env());
    // let evaluate_cond = get_eval_cond(ctx.env());
    let evaluate = Evaluator::new(ctx.env()).unwrap();

    let to_eval = |v: &Variable| {
        if &v.sort == cond {
            evaluate.cond(ctx, svar!(v.clone()))
        } else if &v.sort == msg {
            evaluate.msg(ctx, svar!(v.clone()))
        } else {
            svar!(v.clone())
        }
    };

    debug_assert!(!env.contains_f(&rewriteb));
    declarations.push(Smt::DeclareFun(rewriteb.clone()));

    evaluate_rewrite_conditions(
        env,
        assertions,
        declarations,
        ctx,
        &rewriteb,
        msg,
        cond,
        &to_eval,
        &evaluate,
    );

    if env.no_bitstring_fun() {
        return;
    }

    for f in ctx.ta_funs.iter().filter(|&f| !f.is_special_evaluate()) {
        if &f.get_output_sort() == msg {
            let vars = sorts_to_variables(0, f.input_sorts_iter());
            assertions.push(Smt::DeclareRewrite {
                rewrite_fun: RewriteKind::Other(rewriteb.clone()),
                vars: vars.clone(),
                lhs: Box::new(evaluate.msg(
                    ctx,
                    sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect()),
                )),
                rhs: Box::new(sfun!(
                    f.get_evaluate_function().unwrap(),
                    vars.iter().map(to_eval).collect()
                )),
            })
        } else if &f.get_output_sort() == cond {
            let vars = sorts_to_variables(0, f.input_sorts_iter());
            assertions.push(Smt::DeclareRewrite {
                rewrite_fun: RewriteKind::Bool,
                vars: vars.clone(),
                lhs: Box::new(evaluate.cond(
                    ctx,
                    sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect()),
                )),
                rhs: Box::new(sfun!(
                    f.get_evaluate_function().unwrap(),
                    vars.iter().map(to_eval).collect()
                )),
            })
        } else {
            continue;
        }
    }

    {
        for q in &ctx.pbl.quantifiers {
            // let vars = q.free_variables.iter().chain(q.bound_variables.iter());
            let asserts = match &q.content {
                QuantifierPContent::Exists { content: _ } => vec![
                //     sforall!(
                //     q.free_variables.iter().cloned().collect_vec(),
                //     simplies!(env;
                //         evaluate.cond(ctx,  sfun!(
                //             q.function, q.free_variables.iter().map_into().collect_vec())),
                //         sexists!(
                //             q.bound_variables.iter().cloned().collect_vec(),
                //             evaluate.cond(ctx,  SmtFormula::from(content))
                //         )
                //     )
                // )
                ]
                .into_iter(),
                QuantifierPContent::Forall { content } => vec![sforall!(
                    q.free_variables.iter().cloned().collect_vec(),
                    simplies!(env;
                        evaluate.cond(ctx,  sfun!(
                            q.function, q.free_variables.iter().map_into().collect_vec())),
                        sforall!(
                            q.bound_variables.iter().cloned().collect_vec(),
                            evaluate.cond(ctx,  SmtFormula::from(content))
                        )
                    )
                )]
                .into_iter(),
                QuantifierPContent::FindSuchThat {
                    condition,
                    left,
                    right,
                } => {
                    let sorts = q.function.get_input_sorts();
                    let name = q.function.name();
                    let skolems = q
                        .bound_variables
                        .iter()
                        .map(|Variable { id, sort }| {
                            Function::new_with_flag(
                                &format!("sk${}_{}", name, id),
                                sorts.clone(),
                                sort.clone(),
                                FFlags::SKOLEM,
                            )
                        })
                        .collect_vec();

                    for sk in &skolems {
                        declarations.push(Smt::DeclareFun(sk.clone()));
                    }
                    let bounded_vars_id = q.bound_variables.iter().map(|v| v.id).collect_vec();
                    let sk_args = skolems
                        .iter()
                        .map(|sk| {
                            RichFormula::Fun(
                                sk.clone(),
                                q.free_variables.iter().map_into().collect(),
                            )
                        })
                        .collect_vec();
                    let skolemnise = |formula: &RichFormula| {
                        formula
                            .clone()
                            .apply_substitution(&bounded_vars_id, sk_args.as_slice())
                    };

                    let sk_condition: SmtFormula = skolemnise(condition).into();
                    let left: SmtFormula = skolemnise(left).into();
                    let right: SmtFormula = skolemnise(right).into();
                    let condition: SmtFormula = condition.into();

                    vec![
                        sforall!(
                            q.bound_variables
                                .iter()
                                .chain(q.free_variables.iter())
                                .cloned()
                                .collect(),
                            simplies!(env;
                                evaluate.cond(ctx,  condition),
                                evaluate.cond(ctx,  sk_condition.clone())
                            )
                        ),
                        sforall!(
                            q.free_variables
                                .iter()
                                .map(|v| Variable::clone(v))
                                .collect(),
                            seq!(
                                evaluate.msg(
                                    ctx,
                                    sfun!(
                                        q.function,
                                        q.free_variables.iter().map(SmtFormula::from).collect()
                                    )
                                ),
                                site!(
                                    evaluate.cond(ctx, sk_condition),
                                    evaluate.msg(ctx, left),
                                    evaluate.msg(ctx, right)
                                )
                            )
                        ),
                    ]
                    .into_iter()
                }
            };
            assertions.extend(asserts.map(|a| Smt::Assert(a)));
        }
    }
}

fn evaluate_rewrite_conditions<F /* , F2, F3 */>(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx,
    _rewriteb: &Function,
    msg: &Sort,
    cond: &Sort,
    to_eval: &F,
    evaluate: &Evaluator,
) where
    F: Fn(&Variable) -> SmtFormula,
    // F2: Fn(SmtFormula) -> SmtFormula,
    // F3: Fn(SmtFormula) -> SmtFormula,
{
    let v1 = Variable::new(1, cond.clone());
    let v2 = Variable::new(2, cond.clone());
    let vars = vec![v1.clone(), v2.clone()];

    // and
    {
        let cand = env.get_f(CAND_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(evaluate.cond(ctx, sfun!(cand, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::And(vars.iter().map(to_eval).collect())),
        })
    }
    // or
    {
        let cor = env.get_f(COR_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(evaluate.cond(ctx, sfun!(cor, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::Or(vars.iter().map(to_eval).collect())),
        })
        // assertions.push(Smt::Assert(sforall!(a!1:cond, b!2:cond; {
        //     simplies!(env;
        //         sor!(evaluate.cond(ctx, a.clone()) , evaluate.cond(ctx, a.clone())),
        //         evaluate.cond(ctx, sfun!(cor; a, b))
        //     )
        // })))
    }

    // not
    {
        let cnot = env.get_f(CNOT_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vec![v1.clone()],
            lhs: Box::new(evaluate.cond(ctx, sfun!(cnot; svar!(v1.clone())))),
            rhs: Box::new(snot!(env; to_eval(&v1))),
        })
    }

    // eq
    {
        let v1 = Variable::new(1, msg.clone());
        let v2 = Variable::new(2, msg.clone());
        let vars = vec![v1, v2];
        let ceq = env.get_f(CEQ_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(evaluate.cond(ctx, sfun!(ceq, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::Eq(vars.iter().map(to_eval).collect())),
        })
    }

    // true
    {
        assertions.push(Smt::Assert(
            evaluate.cond(ctx, sfun!(env.get_f(CTRUE_NAME).unwrap())),
        ))
    }

    // false
    {
        assertions.push(Smt::Assert(snot!(env;
            evaluate.cond(ctx,  sfun!(env.get_f(CFALSE_NAME).unwrap()))
        )))
    }

    // ite
    {
        let vars = sorts_to_variables(0, [cond, msg, msg].into_iter());
        let (c, l, r) = (&vars[0], &vars[1], &vars[2]);
        let fite = env.get_f(IF_THEN_ELSE_NAME).unwrap();
        assertions.push(Smt::Assert(sforall!(
            vars.clone(),
            seq!(
                evaluate.msg(
                    ctx,
                    sfun!(fite; svar!(c.clone()), svar!(l.clone()), svar!(r.clone()))
                ),
                site!(to_eval(c), to_eval(l), to_eval(r))
            )
        )))
    }
}

fn user_evaluate(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    for f in &ctx.pbl.assertions {
        assertions.push(Smt::Assert(f.into()))
    }
}
