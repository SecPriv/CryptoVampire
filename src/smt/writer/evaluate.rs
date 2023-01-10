use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{EVAL_COND, EVAL_MSG, IF_THEN_ELSE_NAME},
            types::{BITSTRING, BOOL, CONDITION, MSG},
        },
        env::Environement,
        formula::{sorts_to_variables, RichFormula, Variable},
        function::{FFlags, Function},
    },
    problem::problem::{
        QuantifierPContent, CAND_NAME, CEQ_NAME, CFALSE_NAME, CNOT_NAME, COR_NAME, CTRUE_NAME,
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
    if env.use_rewrite() {
        evaluate_rewrite(env, assertions, declarations, ctx)
    } else {
        let mut masserts = Vec::new();
        evaluate_rewrite(env, &mut masserts, declarations, ctx);
        assertions.extend(masserts.into_iter().map(|a| a.rewrite_to_assert(env)))
    }
    user_evaluate(env, assertions, declarations, ctx)
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
    let evaluate_msg = EVAL_MSG(env);
    let evaluate_cond = EVAL_COND(env);

    let to_eval = |v: &Variable| {
        if &v.sort == cond {
            sfun!(evaluate_cond; svar!(v.clone()))
        } else if &v.sort == msg {
            sfun!(evaluate_msg; svar!(v.clone()))
        } else {
            svar!(v.clone())
        }
    };

    debug_assert!(!env.contains_f(&rewriteb));
    declarations.push(Smt::DeclareFun(rewriteb.clone()));

    for f in ctx.ta_funs.iter().filter(|&f| !f.is_special_evaluate()) {
        if &f.get_output_sort() == msg {
            let vars = sorts_to_variables(0, f.input_sorts_iter());
            assertions.push(Smt::DeclareRewrite {
                rewrite_fun: RewriteKind::Other(rewriteb.clone()),
                vars: vars.clone(),
                lhs: Box::new(
                    sfun!(evaluate_msg; sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect())),
                ),
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
                lhs: Box::new(
                    sfun!(evaluate_cond; sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect())),
                ),
                rhs: Box::new(sfun!(
                    f.get_evaluate_function().unwrap(),
                    vars.iter().map(to_eval).collect()
                )),
            })
        } else {
            continue;
        }
    }

    let v1 = Variable::new(1, cond.clone());
    let v2 = Variable::new(2, cond.clone());
    let vars = vec![v1.clone(), v2.clone()];

    // and
    {
        let cand = env.get_f(CAND_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cand, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::And(vars.iter().map(to_eval).collect())),
        })
    }
    // or
    {
        let cor = env.get_f(COR_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cor, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::Or(vars.iter().map(to_eval).collect())),
        })
    }

    // not
    {
        let cnot = env.get_f(CNOT_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vec![v1.clone()],
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cnot; svar!(v1.clone())))),
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
            lhs: Box::new(sfun!(evaluate_cond; sfun!(ceq, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::Eq(vars.iter().map(to_eval).collect())),
        })
    }

    // true
    {
        assertions.push(Smt::Assert(
            sfun!(evaluate_cond; sfun!(env.get_f(CTRUE_NAME).unwrap())),
        ))
    }

    // false
    {
        assertions.push(Smt::Assert(snot!(env;
            sfun!(evaluate_cond; sfun!(env.get_f(CFALSE_NAME).unwrap()))
        )))
    }

    // ite
    {
        let vars = sorts_to_variables(0, [cond, msg, msg].into_iter());
        let (c, l, r) = (&vars[0], &vars[1], &vars[2]);
        let fite = env.get_f(IF_THEN_ELSE_NAME).unwrap();
        assertions.push(Smt::Assert(sforall!(vars.clone(), seq!(
            sfun!(evaluate_msg; sfun!(fite; svar!(c.clone()), svar!(l.clone()), svar!(r.clone()))),
            site!( to_eval(c), to_eval(l), to_eval(r))
        ))))
    }

    {
        for q in &ctx.pbl.quantifiers {
            // let vars = q.free_variables.iter().chain(q.bound_variables.iter());
            let asserts = match &q.content {
                QuantifierPContent::Exists { content } => vec![sforall!(
                    q.free_variables.iter().cloned().collect_vec(),
                    simplies!(env;
                        sfun!(evaluate_cond; sfun!(
                            q.function, q.free_variables.iter().map_into().collect_vec())),
                        sexists!(
                            q.bound_variables.iter().cloned().collect_vec(),
                            sfun!(evaluate_cond; SmtFormula::from(content))
                        )
                    )
                )]
                .into_iter(),
                QuantifierPContent::Forall { content } => vec![sforall!(
                    q.free_variables.iter().cloned().collect_vec(),
                    simplies!(env;
                        sfun!(evaluate_cond; sfun!(
                            q.function, q.free_variables.iter().map_into().collect_vec())),
                        sforall!(
                            q.bound_variables.iter().cloned().collect_vec(),
                            sfun!(evaluate_cond; SmtFormula::from(content))
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
                                sfun!(evaluate_cond; condition),
                                sfun!(evaluate_cond; sk_condition)
                            )
                        ),
                        sforall!(
                            q.free_variables
                                .iter()
                                .map(|v| Variable::clone(v))
                                .collect(),
                            seq!(
                                sfun!(evaluate_msg; sfun!(
                                        q.function, q.free_variables.iter().map(SmtFormula::from).collect())),
                                site!(
                                    sfun!(evaluate_cond; sk_condition),
                                    sfun!(evaluate_msg; left),
                                    sfun!(evaluate_msg; right)
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
