use std::convert::identity;

use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::problem::crypto_assumptions::aux;
use crate::{
    formula::{
        builtins::{
            functions::{EVAL_COND, EVAL_MSG, INPUT, LT, NONCE_MSG},
            types::{CONDITION, MSG, NONCE},
        },
        formula::{RichFormula, Variable},
        function::{FFlags, Function},
    },
    smt::{
        macros::{sand, seq, sexists, sforall, sfun, simplies, site, sor, srewrite, svar},
        smt::{RewriteKind, Smt, SmtFormula},
        writer::{
            subterm::{default_f, generate_subterm},
            Ctx,
        },
    },
};
pub(crate) fn generate(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    mac: &Function,
    verify: &Function,
) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let eval_cond = EVAL_COND(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let cond = CONDITION(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();
    let input_f = INPUT(ctx.env()).clone();
    let lt = LT(ctx.env()).clone();

    assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg; {
                sfun!(eval_cond; sfun!(verify; sfun!(mac; m.clone(), sfun!(nonce; sk.clone())), m.clone(),  sfun!(nonce; sk.clone())))
        })));

    if ctx.env().preprocessing_plus() {
        // find candidates for preprocessing
        let candidates = ctx
            .pbl
            .iter_content()
            .map(|(_, f)| f)
            .chain(std::iter::once(&ctx.pbl.query))
            .flat_map(|f| {
                f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                    RichFormula::Fun(fun, args) if fun == verify => {
                        if_chain!(
                            if let RichFormula::Fun(f1, k) = &args[2];
                            if f1 == &nonce;
                            then {
                                (Some((&args[0], &args[1], &k[0])), vec![&args[0], &args[1]])
                            } else {
                                (None, args.iter().collect())
                            }
                        )
                    }
                    RichFormula::Fun(_, args) => (None, args.iter().collect()),
                    _ => (None, vec![]),
                })
            })
            .unique()
            .collect_vec();

        for (sigma, m, k) in candidates.into_iter() {
            // println!(
            //     "sigma = {}, m = {}, k = {}",
            //     SmtFormula::from(sigma),
            //     SmtFormula::from(m),
            //     SmtFormula::from(k)
            // );

            // side condtion on k
            let k_sc = {
                let kfun = if let RichFormula::Fun(f, _) = k {
                    f
                } else {
                    unreachable!()
                };

                let tmp = ctx
                    .pbl
                    .iter_content()
                    .map(|(_, f)| f)
                    .chain([sigma, m].into_iter())
                    .flat_map(|f| {
                        f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                            RichFormula::Fun(fun, _) if fun == kfun => (Some(()), vec![]),
                            RichFormula::Fun(fun, args) if fun == verify || fun == mac => {
                                (None, args.iter().rev().skip(1).collect())
                            }
                            RichFormula::Fun(_, args) => (None, args.iter().collect()),
                            _ => (None, vec![]),
                        })
                    })
                    .next()
                    .is_none();
                tmp
            };

            if k_sc {
                // free vars of k
                // let fv = k.get_free_vars().into_iter().cloned().collect_vec();
                let fv = k
                    .get_free_vars()
                    .into_iter()
                    .chain(m.get_free_vars().into_iter())
                    .chain(sigma.get_free_vars().into_iter())
                    .unique()
                    .cloned()
                    .collect_vec();

                let max_var = fv
                    .iter()
                    .map(|v| v.id)
                    // .chain(m.get_free_vars().iter().map(|v| v.id))
                    .max()
                    .unwrap_or(0);

                // let u = Variable {
                //     id: max_var + 1,
                //     sort: msg.clone(),
                // };
                // let su = svar!(u.clone());
                let sk = SmtFormula::from(k);
                let sm = SmtFormula::from(m);
                let ssigma = SmtFormula::from(sigma);

                let max_var = max_var + 1;

                let (
                    mut candidates, // the hashes find in m and sigma (might be filtered out later)
                    inputs,         // the input(s) encountered
                ): (Vec<_>, Vec<_>) = [m, sigma]
                    .into_iter()
                    .flat_map(|f| {
                        f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                            RichFormula::Fun(fun, args) if fun == mac => (
                                Some(Either::Left((None, &args[0], &args[1]))),
                                args.iter().collect(),
                            ),
                            RichFormula::Fun(fun, args) if fun == &input_f => {
                                (Some(Either::Right(&args[0])), vec![])
                            }
                            RichFormula::Fun(_, args) => (None, args.iter().collect()),
                            _ => (None, vec![]),
                        })
                    })
                    .partition_map(identity);

                if !inputs.is_empty() {
                    // if there were no inputs in m and sigma, no need to explore the whole protocol !
                    candidates.extend(ctx.pbl.iter_content().flat_map(|(s, f)| {
                        f.custom_iter_w_quantifier(&ctx.pbl, move |f, _| match f {
                            RichFormula::Fun(fun, args) if fun == mac => {
                                (Some((Some(s), &args[0], &args[1])), args.iter().collect())
                            }
                            RichFormula::Fun(_, args) => (None, args.iter().collect()),
                            _ => (None, vec![]),
                        })
                    }))
                }

                let inputs = inputs
                    .into_iter()
                    .unique()
                    .map(|f| SmtFormula::from(f))
                    .collect_vec();

                let ors = candidates
                    .into_iter()
                    .map(|(s, m2, k2)| {
                        let m2 = m2.translate_vars(max_var);
                        let k2 = k2.translate_vars(max_var);

                        let sm2 = SmtFormula::from(&m2);
                        let sk2 = SmtFormula::from(&k2);

                        match s {
                            None => {
                                let nvars = m2
                                    .get_free_vars()
                                    .into_iter()
                                    .chain(k2.get_free_vars().into_iter())
                                    .unique()
                                    .cloned()
                                    .collect_vec();
                                // let ss = sfun!(s.function().clone(), svars.map(|v| svar!(v)).collect());

                                SmtFormula::Exists(
                                    nvars,
                                    Box::new(sand!(
                                        // seq!(su.clone(), m2),
                                        seq!(sfun!(nonce; sk.clone()), sk2),
                                        seq!(sfun!(eval_msg; sm2), sfun!(eval_msg; sm.clone()))
                                    )),
                                )
                            }
                            Some(s) => {
                                let nvars = s
                                    .occuring_variables()
                                    .iter()
                                    .map(|v| Variable {
                                        id: v.id + max_var,
                                        ..v.clone()
                                    })
                                    .collect_vec();
                                let svars = s
                                    .free_variables()
                                    .iter()
                                    .map(|v| Variable {
                                        id: v.id + max_var,
                                        ..v.clone()
                                    })
                                    .map(|v| svar!(v))
                                    .collect_vec();

                                let ss = sfun!(s.function().clone(), svars);

                                let s_ors = inputs
                                    .iter()
                                    .map(|is| sfun!(lt; ss.clone(), is.clone()))
                                    .collect();

                                SmtFormula::Exists(
                                    nvars,
                                    Box::new(sand!(
                                        SmtFormula::Or(s_ors),
                                        seq!(sfun!(nonce; sk.clone()), sk2),
                                        seq!(sfun!(eval_msg; sm2), sfun!(eval_msg; sm.clone()))
                                    )),
                                )
                            }
                        }
                    })
                    .collect();

                assertions.push(Smt::Assert(SmtFormula::Forall(
                    fv,
                    Box::new(simplies!(ctx.env();
                        sfun!(eval_cond; sfun!(verify;ssigma, sm.clone(), sfun!(nonce; sk.clone()))),
                        // SmtFormula::Exists(vec![u], Box::new(SmtFormula::Or(ors))))),
                        SmtFormula::Or(ors))),
                )))
            }
        }
    } else if !ctx.env().no_ta() {
        let subt_main = generate_subterm(
            assertions,
            declarations,
            ctx,
            "sbt$euf_hash_main",
            &msg,
            vec![],
            default_f(),
        );
        let subt_sec = generate_subterm(
            assertions,
            declarations,
            ctx,
            "sbt$euf_hash_sec",
            &nonce_sort,
            vec![mac, verify],
            |_, m, _, _, f| match f {
                RichFormula::Var(v) if v.sort == nonce_sort => (Some(aux(m, f)), vec![]),
                RichFormula::Fun(fun, args) if fun == mac => {
                    let mut todo = Vec::with_capacity(2);
                    todo.push(&args[0]);
                    if_chain!(
                        if let RichFormula::Fun(fun2, _) = &args[1];
                        if fun2 == &nonce;
                        then {}
                        else {
                            todo.push(&args[1])
                        }
                    );
                    (None, todo)
                }
                RichFormula::Fun(fun, args) if fun == verify => {
                    let mut todo = Vec::with_capacity(3);
                    todo.push(&args[0]);
                    todo.push(&args[1]);
                    if_chain!(
                        if let RichFormula::Fun(fun2, _) = &args[2];
                        if fun2 == &nonce;
                        then {}
                        else {
                            todo.push(&args[2])
                        }
                    );
                    (None, todo)
                }
                RichFormula::Fun(fun, args) => (
                    (fun.get_output_sort() == nonce_sort).then(|| aux(m, f)),
                    args.iter().collect(),
                ),
                _ => (None, vec![]),
            },
        );

        for s in subt_sec.iter() {
            assertions.push(Smt::Assert(sforall!(k!0:nonce_sort, m!1:msg, k2!2:msg; {
                simplies!(ctx.env();
                    s.f(k.clone(), sfun!(mac; m.clone(), k2.clone()), &msg),
                    site!(
                        seq!(k2.clone(), sfun!(nonce; k.clone())),
                        s.f(k.clone(), m.clone(), &msg),
                        sor!(
                            s.f(k.clone(), m.clone(), &msg),
                            s.f(k.clone(), k2.clone(), &msg)
                        )
                    )
                )
            })));

            assertions.push(Smt::Assert(
                sforall!(k!0:nonce_sort, sigma!3:msg, m!1:msg, k2!2:msg; {
                    simplies!(ctx.env();
                        s.f(k.clone(), sfun!(verify; m.clone(), sigma.clone(), k2.clone()), &cond),
                        site!(
                            seq!(k2.clone(), sfun!(nonce; k.clone())),
                            sor!(
                                s.f(k.clone(), m.clone(), &msg),
                                s.f(k.clone(), sigma.clone(), &msg)
                            ),
                            sor!(
                                s.f(k.clone(), m.clone(), &msg),
                                s.f(k.clone(), k2.clone(), &msg),
                                s.f(k.clone(), sigma.clone(), &msg)
                            )
                        )
                    )
                }),
            ))
        }

        if ctx.env().crypto_rewrite() {
            let sk = Function::new_with_flag(
                "sk$u$euf_cma",
                vec![msg.clone(), msg.clone(), nonce_sort.clone()],
                msg.clone(),
                FFlags::SKOLEM,
            );
            let asser = srewrite!(
                    RewriteKind::Bool; s!1:msg, k!2:nonce_sort, m!3:msg;
                    {
                        // seq!(
                        //     sfun!(eval_msg; s.clone()),
                        //     sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                        // )
                        sfun!(eval_cond; sfun!(verify; s.clone(), m.clone(), sfun!(nonce; k.clone())))
                    } -> {
                        let u = sfun!(sk; s.clone(), m.clone(), k.clone());
                        let h = sfun!(mac; u.clone(), sfun!(nonce; k.clone()));
                        sand!(
                            sor!(
                                subt_main.f(h.clone(), s.clone(), &msg),
                                subt_main.f(h.clone(), m.clone(), &msg),
                                subt_sec.f(k.clone(), m.clone(), &msg),
                                subt_sec.f(k.clone(), s.clone(), &msg)
                            ),
                            seq!(sfun!(eval_msg; m.clone()), sfun!(eval_msg; u.clone()))
                        )
                    }
            );

            declarations.push(Smt::DeclareFun(sk));
            assertions.push(asser);
        } else {
            let asser = sforall!(s!1:msg, k!2:nonce_sort, m!3:msg;{
                    simplies!(ctx.env();
                        // seq!(
                        //     sfun!(eval_msg; s.clone()),
                        //     sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                        // )
                        sfun!(eval_cond; sfun!(verify; s.clone(), m.clone(), sfun!(nonce; k.clone())))
                    ,
                        sexists!(u!4:msg; {
                        let h = sfun!(mac; u.clone(), sfun!(nonce; k.clone()));
                        sand!(
                            sor!(
                                subt_main.f(h.clone(), s.clone(), &msg),
                                subt_main.f(h.clone(), m.clone(), &msg),
                                subt_sec.f(k.clone(), m.clone(), &msg),
                                subt_sec.f(k.clone(), s.clone(), &msg)
                            ),
                            seq!(sfun!(eval_msg; m.clone()), sfun!(eval_msg; u.clone()))
                        )})
                    )}
            );
            assertions.push(Smt::Assert(asser));
        }
    }
}
