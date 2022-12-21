use std::collections::HashMap;

use itertools::{Either, Itertools};

use crate::{
    formula::{
        builtins::{
            functions::{
                EVAL_COND_NAME, EVAL_MSG_NAME, HAPPENS, HAPPENS_NAME, IF_THEN_ELSE,
                IF_THEN_ELSE_NAME, LT_NAME,
            },
            steps::INIT,
            types::{BITSTRING, BOOL, CONDITION, MSG, NONCE, STEP},
        },
        env::Environement,
        formula::{sorts_to_variables, RichFormula, Variable},
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::problem::{
        Problem, QuantifierPContent, CAND_NAME, CEQ_NAME, CFALSE_NAME, CNOT_NAME, COR_NAME,
        CTRUE_NAME,
    },
    smt::smt::RewriteKind,
};

use super::{
    macros::*,
    smt::{Smt, SmtCons, SmtFormula},
};

struct Ctx<'a> {
    ta_funs: Vec<&'a Function>,
    free_funs: Vec<&'a Function>,
    ta_sorts: Vec<&'a Sort>,
    free_sorts: Vec<&'a Sort>,
    pbl: &'a Problem,
}

pub fn problem_to_smt(env: &Environement, mut pbl: Problem) -> Vec<Smt> {
    let Problem {
        steps,
        functions,
        sorts,
        assertions,
        query,
        order,
        lemmas,
        crypto_assumptions,
        quantifiers,
    } = &pbl;

    let mut declarations = Vec::new();
    let mut assertions = Vec::new();

    let (ta_funs, free_funs): (Vec<_>, Vec<_>) = functions.into_iter().partition_map(|(_, f)| {
        if f.is_term_algebra() {
            Either::Left(f)
        } else {
            Either::Right(f)
        }
    });
    let (ta_sorts, free_sorts): (Vec<_>, Vec<_>) = sorts.into_iter().partition_map(|s| {
        if s.is_term_algebra() {
            Either::Left(s)
        } else {
            Either::Right(s)
        }
    });

    let mut ctx = Ctx {
        ta_funs,
        free_funs,
        ta_sorts,
        free_sorts,
        pbl: &pbl,
    };

    // declare sorts and funs
    declare(env, &mut assertions, &mut declarations, &ctx);

    // nonce pseudo ta
    nonce_pseudo_ta(env, &mut assertions, &mut declarations, &ctx);

    // ordering
    ordering(env, &mut assertions, &mut declarations, &ctx);

    // evaluate
    evaluate(env, &mut assertions, &mut declarations, &ctx);

    declarations.extend(assertions.into_iter());
    declarations
}

fn declare(
    _env: &Environement,
    _assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let free_sorts = &ctx.free_sorts;
    let ta_sorts = &ctx.ta_sorts;
    let free_funs = &ctx.free_funs;
    let ta_funs = &ctx.ta_funs;

    // free sorts
    declarations.extend(
        free_sorts
            .into_iter()
            .filter_map(|&s| (!s.is_built_in()).then_some(Smt::DeclareSort(s.clone()))),
    );

    // ta
    let cons = ta_sorts
        .iter()
        .map(|&s| {
            ta_funs
                .iter()
                .filter(|&&f| f.get_output_sort() == s)
                .map(|&f| SmtCons {
                    fun: f.clone(),
                    dest: f.generate_new_destructor(),
                })
                .collect_vec()
        })
        .collect_vec();
    declarations.push(Smt::DeclareDatatypes {
        sorts: ta_sorts.iter().map(|&s| s.clone()).collect(),
        cons,
    });

    // free funs
    declarations.extend(
        free_funs
            .iter()
            .filter_map(|&f| (!f.is_built_in()).then_some(Smt::DeclareFun(f.clone()))),
    );
}

fn nonce_pseudo_ta(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let free_funs = &ctx.free_funs;
    let nonce = NONCE.clone();
    let nonces = free_funs
        .iter()
        .filter(|&&f| f.get_output_sort() == &nonce)
        .map(|&f| f)
        .collect_vec();

    assertions.push({
        let mut i = 0;
        let (vars, nonces): (Vec<_>, Vec<_>) = nonces
            .iter()
            .map(|&f| {
                let vars = f
                    .get_input_sorts()
                    .iter()
                    .map(|s| {
                        i += 1;
                        Variable {
                            id: i,
                            sort: s.clone(),
                        }
                    })
                    .collect_vec();
                (
                    vars.clone(),
                    SmtFormula::Fun(
                        f.clone(),
                        vars.into_iter().map(|v| SmtFormula::Var(v)).collect_vec(),
                    ),
                )
            })
            .unzip();

        let vars = vars.into_iter().flat_map(|v| v.into_iter()).collect_vec();

        Smt::Assert(sforall!(vars, SmtFormula::Neq(nonces)))
    });

    for n in nonces {
        let vars1 = n
            .get_input_sorts()
            .iter()
            .enumerate()
            .map(|(id, s)| Variable {
                id,
                sort: s.clone(),
            })
            .collect_vec();
        let vars2 = vars1
            .iter()
            .map(|v| Variable {
                id: vars1.len() + v.id,
                sort: v.sort.clone(),
            })
            .collect_vec();

        assertions.push(Smt::Assert(sforall!(
            vars1
                .iter()
                .chain(vars2.iter())
                .map(|v| v.clone())
                .collect_vec(),
            simplies!(
                seq!(
                    sfun!(n, vars1.iter().map_into().collect()),
                    sfun!(n, vars2.iter().map_into().collect())
                ),
                SmtFormula::Or(
                    vars1
                        .into_iter()
                        .zip(vars2.into_iter())
                        .map(|(v1, v2)| { seq!(svar!(v1), svar!(v2)) })
                        .collect_vec()
                )
            )
        )))
    }
}

fn ordering(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let functions = &ctx.pbl.functions;
    let init = sfun!(functions.get(INIT.name()).unwrap().clone());
    let lt = functions.get(LT_NAME).unwrap().clone();
    let happens = functions.get(HAPPENS_NAME).unwrap().clone();

    assertions.push(Smt::AssertTh(sforall!(s!0:STEP; {
        sor!(
            sfun!(lt; init, s),
            seq!(init, s)
        )
    })));
    assertions.push(Smt::AssertTh(sforall!(s1!1:STEP, s2!2:STEP, s3!3:STEP ;{
            simplies!(
                sand!(
                    sfun!(lt; s1, s2),
                    sfun!(lt; s2, s3)
                ),
                sfun!(lt; s1, s3)
            )
    })));
    assertions.push(Smt::AssertTh(sforall!(s1!1:STEP, s2!2:STEP; {
        simplies!(
            sand!(
                sfun!(happens; s2),
                sfun!(lt; s1, s2)
            ),
            sfun!(happens; s1)
        )
    })));
}

fn evaluate(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    if env.use_rewrite {
        evaluate_rewrite(env, assertions, declarations, ctx)
    } else {
        todo!()
    }
}
fn evaluate_rewrite(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let msg = MSG.clone();
    let cond = CONDITION.clone();
    let rewriteb = Function::new(
        "r$rewriteb",
        vec![BITSTRING.clone(), BITSTRING.clone()],
        BOOL.clone(),
    );
    let functions = &ctx.pbl.functions;
    let evaluate_msg = functions.get(EVAL_MSG_NAME).unwrap();
    let evaluate_cond = functions.get(EVAL_COND_NAME).unwrap();

    let to_eval = |v: &Variable| {
        if &v.sort == &cond {
            sfun!(evaluate_cond; svar!(v.clone()))
        } else if &v.sort == &msg {
            sfun!(evaluate_msg; svar!(v.clone()))
        } else {
            svar!(v.clone())
        }
    };

    debug_assert!(!ctx.pbl.functions.contains_key(rewriteb.name()));
    declarations.push(Smt::DeclareFun(rewriteb.clone()));

    for &f in ctx.ta_funs.iter().filter(|&&f| !f.is_special_evaluate()) {
        if f.get_output_sort() == &msg {
            let vars = sorts_to_variables(0, f.get_input_sorts().into_iter());
            assertions.push(Smt::DeclareRewrite {
                rewrite_fun: RewriteKind::Other(rewriteb.clone()),
                vars: vars.clone(),
                lhs: Box::new(
                    sfun!(evaluate_msg; sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect())),
                ),
                rhs: Box::new(sfun!(
                    f.get_evaluate_function(functions).unwrap(),
                    vars.iter().map(to_eval).collect()
                )),
            })
        } else if f.get_output_sort() == &cond {
            let vars = sorts_to_variables(0, f.get_input_sorts().into_iter());
            assertions.push(Smt::DeclareRewrite {
                rewrite_fun: RewriteKind::Bool,
                vars: vars.clone(),
                lhs: Box::new(
                    sfun!(evaluate_cond; sfun!(f, vars.iter().map(|s| svar!(s.clone())).collect())),
                ),
                rhs: Box::new(sfun!(
                    f.get_evaluate_function(functions).unwrap(),
                    vars.iter().map(to_eval).collect()
                )),
            })
        } else {
            continue;
        }
    }

    let v1 = Variable::new(1, CONDITION.clone());
    let v2 = Variable::new(2, CONDITION.clone());
    let vars = vec![v1.clone(), v2.clone()];

    // and
    {
        let cand = functions.get(CAND_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cand, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::And(vars.iter().map(to_eval).collect())),
        })
    }
    // or
    {
        let cor = functions.get(COR_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vars.clone(),
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cor, vars.iter().map_into().collect()))),
            rhs: Box::new(SmtFormula::Or(vars.iter().map(to_eval).collect())),
        })
    }

    // not
    {
        let cnot = functions.get(CNOT_NAME).unwrap();
        assertions.push(Smt::DeclareRewrite {
            rewrite_fun: RewriteKind::Bool,
            vars: vec![v1.clone()],
            lhs: Box::new(sfun!(evaluate_cond; sfun!(cnot; svar!(v1.clone())))),
            rhs: Box::new(snot!(to_eval(&v1))),
        })
    }

    // eq
    {
        let v1 = Variable::new(1, MSG.clone());
        let v2 = Variable::new(2, MSG.clone());
        let vars = vec![v1, v2];
        let ceq = functions.get(CEQ_NAME).unwrap();
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
            sfun!(evaluate_cond; sfun!(functions.get(CTRUE_NAME).unwrap())),
        ))
    }

    // false
    {
        assertions.push(Smt::Assert(snot!(
            sfun!(evaluate_cond; sfun!(functions.get(CFALSE_NAME).unwrap()))
        )))
    }

    // ite
    {
        let vars = sorts_to_variables(0, [&cond, &msg, &msg].into_iter());
        let (c, l, r) = (&vars[0], &vars[1], &vars[2]);
        let fite = functions.get(IF_THEN_ELSE_NAME).unwrap();
        assertions.push(Smt::Assert(sforall!(vars.clone(), seq!(
            sfun!(evaluate_msg; sfun!(fite; svar!(c.clone()), svar!(l.clone()), svar!(r.clone()))),
            site!(to_eval(c), to_eval(l), to_eval(r))
        ))))
    }

    {
        for q in &ctx.pbl.quantifiers {
            let vars = q.free_variables.iter().chain(q.bound_variables.iter());
            let asserts = match &q.content {
                QuantifierPContent::Exists { content } => vec![sforall!(
                    q.free_variables.iter().cloned().collect_vec(),
                    simplies!(
                        sfun!(evaluate_cond; sfun!(
                            q.function, 
                            q.free_variables.iter().map_into().collect_vec())),
                        sexists!(
                            q.bound_variables.iter().cloned().collect_vec(),
                            sfun!(evaluate_cond; SmtFormula::from(content))
                        )
                    )
                )]
                .into_iter(),
                QuantifierPContent::Forall { content } => vec![sforall!(
                    q.free_variables.iter().cloned().collect_vec(),
                    simplies!(
                        sfun!(evaluate_cond; sfun!(
                            q.function, 
                            q.free_variables.iter().map_into().collect_vec())),
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
                                sorts.into(),
                                sort.clone(),
                                FFlags::SKOLEM,
                            )
                        })
                        .collect_vec();

                    for sk in &skolems {
                        declarations.push(Smt::DeclareFun(sk.clone()));
                    }

                    let skolemnise = |formula: &RichFormula| {
                        skolems
                            .iter()
                            .zip(q.bound_variables.iter())
                            .fold(formula.clone(), |f, (sk, v)| {
                                f.apply(v, &RichFormula::Fun(sk.clone(), vec![]))
                            })
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
                            simplies!(
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
                                        q.function, 
                                        q.free_variables.iter().map(SmtFormula::from).collect())),
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


