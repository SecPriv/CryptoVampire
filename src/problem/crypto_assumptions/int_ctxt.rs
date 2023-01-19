use std::convert::identity;

use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::problem::crypto_assumptions::aux;
use crate::{
    formula::{
        builtins::{
            functions::{EVAL_COND, EVAL_MSG, INPUT, LT, NONCE_MSG},
            types::{BOOL, CONDITION, MSG, NONCE},
        },
        env::Environement,
        formula::{RichFormula, Variable},
        function::{FFlags, Function},
        sort::Sort,
        unifier::Unifier,
    },
    problem::protocol::Step,
    smt::{
        macros::{
            sand, seq, sexists, sforall, sfun, simplies, site, sneq, snot, sor, srewrite, svar,
        },
        smt::{RewriteKind, Smt, SmtFormula},
        writer::{
            subterm::{default_f, generate_subterm, Subterm},
            Ctx,
        },
    },
};

pub(crate) fn generate(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    enc: &Function,
    dec: &Function,
    verify: &Function,
    fail: &Function,
) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let eval_cond = EVAL_COND(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let cond = CONDITION(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();
    let input_f = INPUT(ctx.env()).clone();
    let lt = LT(ctx.env()).clone();

    assertions.push(Smt::Assert(sforall!(m!0:msg, r!1:msg, sk!2:msg; {
        // let r = sfun!(nonce; r);
        // let sk = sfun!(nonce; sk);
            seq!(
                sfun!(eval_msg; sfun!(dec; sfun!(enc; m.clone(), r, sk.clone()), sk)),
                sfun!(eval_msg; m.clone())
            )
    })));

    assertions.push(Smt::Assert(sforall!(m!0:msg, r!1:msg, sk!2:msg; {
        // let r = sfun!(nonce; r);
        // let sk = sfun!(nonce; sk);
        sor!(
            sfun!(eval_cond; sfun!(verify; sfun!(enc; m.clone(), r, sk.clone()), sk.clone())),
            seq!(sfun!(eval_msg; m.clone()), sfun!(eval_msg; sfun!(fail)))
        )
    })));

    assertions.push(Smt::Assert(sforall!(m!0:msg, sk!1:msg; {
        seq!(
            sneq!(sfun!(eval_msg; sfun!(dec; m, sk)), sfun!(eval_msg; sfun!(fail))),
            sfun!(eval_cond; sfun!(verify; m, sk))
        )
    })));

    if !senc_rand(ctx, enc, dec, verify, fail) {
        return;
    }

    if ctx.env().preprocessing_plus() {
        let candidates = ctx
            .pbl
            .iter_content()
            .map(|(_, f)| f)
            .chain(std::iter::once(&ctx.pbl.query))
            .flat_map(|f| {
                f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                    RichFormula::Fun(fun, args) if fun == verify => {
                        println!("here {}", SmtFormula::from(f));
                        if_chain!(
                            if let RichFormula::Fun(f1, k) = &args[1];
                            if f1 == &nonce;
                            then {
                                println!("h");
                                (Some((&args[0], &k[0])), vec![&args[0]])
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
        dbg!(candidates.len());

        for (c, k) in candidates {
            println!("m = {}, k = {}", SmtFormula::from(c), SmtFormula::from(k));

            let kfun = if let RichFormula::Fun(f, _) = k {
                f
            } else {
                unreachable!()
            };

            let side_condition_key = ctx
                .pbl
                .iter_content()
                .map(|(_, f)| f)
                .chain(std::iter::once(c))
                .flat_map(|f| {
                    f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                        RichFormula::Fun(fun, _) if fun == kfun => {
                            println!("{}", SmtFormula::from(f));
                            (Some(()), vec![])
                        }
                        RichFormula::Fun(fun, args)
                            if fun == verify || fun == enc || fun == dec =>
                        {
                            (None, args.iter().rev().skip(1).collect())
                        }
                        RichFormula::Fun(_, args) => (None, args.iter().collect()),
                        _ => (None, vec![]),
                    })
                })
                .next()
                .is_none();

            if !side_condition_key {
                dbg!(side_condition_key);
                continue;
            }
            // free variables
            let fv = k
                .get_free_vars()
                .into_iter()
                .chain(c.get_free_vars().into_iter())
                .unique()
                .cloned()
                .collect_vec();

            let max_var = fv
                .iter()
                .map(|v| v.id)
                // .chain(m.get_free_vars().iter().map(|v| v.id))
                .max()
                .unwrap_or(0);

            let sk = SmtFormula::from(k);
            let sc = SmtFormula::from(c);

            let (mut candidates, inputs): (Vec<_>, Vec<_>) = [c]
                .into_iter()
                .flat_map(|f| {
                    f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                        RichFormula::Fun(fun, args) if fun == enc => (
                            Some(Either::Left((None, &args[0], &args[1], &args[2]))),
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
                candidates.extend(ctx.pbl.iter_content().flat_map(|(s, f)| {
                    f.custom_iter_w_quantifier(&ctx.pbl, move |f, _| match f {
                        RichFormula::Fun(fun, args) if fun == enc => (
                            Some((Some(s), &args[0], &args[1], &args[2])),
                            args.iter().collect(),
                        ),
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
                .map(|(s, m2, r2, k2)| {
                    let m2 = m2.translate_vars(max_var);
                    let k2 = k2.translate_vars(max_var);
                    let r2 = r2.translate_vars(max_var);

                    let sm2 = SmtFormula::from(&m2);
                    let sk2 = SmtFormula::from(&k2);
                    let sr2 = SmtFormula::from(&r2);

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
                                    seq!(
                                        sfun!(eval_msg; sc),
                                        sfun!(eval_msg; sfun!(enc; sm2, sr2, sk2))
                                    )
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
                                    seq!(
                                        sfun!(eval_msg; sc),
                                        sfun!(eval_msg; sfun!(enc; sm2, sr2, sk2))
                                    )
                                )),
                            )
                        }
                    }
                })
                .collect();

            assertions.push(Smt::Assert(SmtFormula::Forall(
                fv,
                Box::new(simplies!(ctx.env();
                        sfun!(eval_cond; sfun!(verify; sc.clone(), sfun!(nonce; sk.clone()))),
                        SmtFormula::Exists(vec![], Box::new(SmtFormula::Or(ors))))),
            )))
        }
    } else if !ctx.env().no_ta() {
        let subt_main = generate_subterm(
            assertions,
            declarations,
            ctx,
            "sbt$euf_ctxt_main",
            &msg,
            vec![],
            default_f(),
        );
        let subt_sk = generate_subterm(
            assertions,
            declarations,
            ctx,
            "sbt$euf_ctxt_sk",
            &nonce_sort,
            vec![enc, dec, verify],
            |_, m, _, _, f| match f {
                RichFormula::Var(v) if v.sort == nonce_sort => (Some(aux(m, f)), vec![]),
                RichFormula::Fun(fun, args) if fun == enc => {
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
                RichFormula::Fun(fun, args) if fun == dec || fun == verify => {
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
                RichFormula::Fun(fun, args) => (
                    (fun.get_output_sort() == nonce_sort).then(|| aux(m, f)),
                    args.iter().collect(),
                ),
                _ => (None, vec![]),
            },
        );
        let subt_rd = generate_subterm(
            assertions,
            declarations,
            ctx,
            "sbt$euf_ctxt_r",
            &nonce_sort,
            vec![enc],
            |_, m, _, _, f| match f {
                RichFormula::Var(v) if v.sort == nonce_sort => (Some(aux(m, f)), vec![]),
                RichFormula::Fun(fun, args) if fun == enc => {
                    let mut todo = Vec::with_capacity(3);
                    todo.push(&args[0]);
                    todo.push(&args[2]);
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
                RichFormula::Fun(fun, args) => (
                    (fun.get_output_sort() == nonce_sort).then(|| aux(m, f)),
                    args.iter().collect(),
                ),
                _ => (None, vec![]),
            },
        );

        for s in subt_sk.iter() {
            assertions.push(Smt::Assert(
                sforall!(sk!0:nonce_sort, k!1:msg, m!2:msg, r!3:msg;{
                    simplies!(ctx.env();
                        s.f(sk.clone(), sfun!(enc; m.clone(), r.clone(), k.clone()), &msg),
                        site!(
                            seq!(k.clone(), sfun!(nonce; sk.clone())),
                            sor!(
                                s.f(sk.clone(), m.clone(), &msg),
                                s.f(sk.clone(), r.clone(), &msg)
                            ),
                            sor!(
                                s.f(sk.clone(), m.clone(), &msg),
                                s.f(sk.clone(), r.clone(), &msg),
                                s.f(sk.clone(), k.clone(), &msg)
                            )
                        )
                    )
                }),
            ));
            assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg, k!2:msg; {
                simplies!(ctx.env();
                    s.f(sk.clone(), sfun!(dec; m.clone(), k.clone()), &msg),
                    site!(
                        seq!(k.clone(), sfun!(nonce; sk.clone())),
                        s.f(sk.clone(), m.clone(), &msg),
                        sor!(
                            s.f(sk.clone(), m.clone(), &msg),
                            s.f(sk.clone(), k.clone(), &msg)
                        )
                    )
                )
            })));
            assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg, k!2:msg; {
                simplies!(ctx.env();
                    s.f(sk.clone(), sfun!(verify; m.clone(), k.clone()), &cond),
                    site!(
                        seq!(k.clone(), sfun!(nonce; sk.clone())),
                        s.f(sk.clone(), m.clone(), &msg),
                        sor!(
                            s.f(sk.clone(), m.clone(), &msg),
                            s.f(sk.clone(), k.clone(), &msg)
                        )
                    )
                )
            })))
        }

        for s in subt_rd.iter() {
            assertions.push(Smt::Assert(
                sforall!(nr!0:nonce_sort, k!1:msg, m!2:msg, r!3:msg;{
                    simplies!(ctx.env();
                        s.f(nr.clone(), sfun!(enc; m.clone(), r.clone(), k.clone()), &msg),
                        site!(
                            seq!(r.clone(), sfun!(nonce; nr.clone())),
                            sor!(
                                s.f(nr.clone(), m.clone(), &msg),
                                s.f(nr.clone(), k.clone(), &msg)
                            ),
                            sor!(
                                s.f(nr.clone(), m.clone(), &msg),
                                s.f(nr.clone(), r.clone(), &msg),
                                s.f(nr.clone(), k.clone(), &msg)
                            )
                        )
                    )
                }),
            ));
        }

        // assertions.push(Smt::Assert(
        //     sforall!(m!0:msg, r!1:nonce_sort, sk!2:nonce_sort; {
        //         let r = sfun!(nonce; r);
        //         let sk = sfun!(nonce; sk);
        //         seq!(
        //             snot!(ctx.env(); sfun!(eval_cond; sfun!(verify; m.clone(), sk.clone()))),
        //             seq!(sfun!(eval_msg; sfun!(fail;)), sfun!(eval_msg; sfun!(dec; m.clone(), sk.clone())))
        //         )
        //     })
        // ));

        // let sp = Function::new_with_flag(
        //     "sp$int_ctxt",
        //     vec![nonce_sort.clone(), msg.clone()],
        //     BOOL(ctx.env()).clone(),
        //     FFlags::empty(),
        // );
        // declarations.push(Smt::DeclareFun(sp.clone()));

        // // let's ignore this for now
        // if false {
        //     assertions.push(Smt::Assert(sforall!(c!0:msg, k!1:nonce_sort; {
        //         simplies!(ctx.env();
        //             // sand!(
        //             //     sfun!(sp; k.clone(), c.clone()),
        //             //     subt_main.main(sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg)
        //             // ),
        //             sfun!(sp; k.clone(), c.clone()),
        //             sexists!( r!2:msg, m!3:msg;{
        //                 sand!(
        //                     subt_main.main(sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg),
        //                     sor!(
        //                         sforall!(n!4:nonce_sort; {sneq!(r.clone(), sfun!(nonce; n))}),
        //                         sexists!(m2!4:msg, k2!5:msg; {
        //                             sand!(
        //                                 subt_main.main(sfun!(enc; m2.clone(), r.clone(), k2.clone()), c.clone(), &msg),
        //                                 sneq!(m2, m.clone()),
        //                                 sneq!(k2,  sfun!(nonce; k.clone()))
        //                             )
        //                         }),
        //                         sexists!(n!4:nonce_sort; {sand!(
        //                             seq!(r.clone(), sfun!(nonce; n.clone())),
        //                             subt_rd.main(n.clone(), c.clone(), &msg)
        //                         )})
        //                     )
        //                 )
        //             })
        //         )
        //     })));
        // }

        if ctx.env().crypto_rewrite() {
            let sk_m = Function::new_with_flag(
                "sk$u$int_ctx_m",
                vec![msg.clone(), nonce_sort.clone()],
                msg.clone(),
                FFlags::SKOLEM,
            );
            let sk_r = Function::new_with_flag(
                "sk$u$int_ctx_r",
                vec![msg.clone(), nonce_sort.clone()],
                nonce_sort.clone(),
                FFlags::SKOLEM,
            );

            declarations.push(Smt::DeclareFun(sk_m.clone()));
            declarations.push(Smt::DeclareFun(sk_r.clone()));

            assertions.push(srewrite!(
            RewriteKind::Bool; c!2:msg, k!3:nonce_sort;
            {
                // sneq!(
                //     sfun!(eval_msg; sfun!(fail; )),
                //     sfun!(eval_msg; sfun!(dec; c.clone(), sfun!(nonce; k.clone())))
                // )
                sfun!(eval_cond; sfun!(verify; c.clone(), sfun!(nonce; k.clone())))
            } -> {
                let m = sfun!(sk_m; c.clone(), k.clone());
                let r = sfun!(sk_r; c.clone(), k.clone());
                let nc = sfun!(enc; m.clone(), sfun!(nonce; r.clone()), sfun!(nonce; k.clone()));
                sor!(
                    subt_sk.main(k.clone(), c.clone(), &msg),
                    subt_main.main(nc, c.clone(), &msg) //,
                    // sfun!(sp; k.clone(), c.clone())
                )
            }
        ));
        } else {
            assertions.push(Smt::Assert(sforall!(c!2:msg, k!3:nonce_sort;{
                simplies!(ctx.env();
                    // sneq!(
                    //     sfun!(eval_msg; sfun!(fail; )),
                    //     sfun!(eval_msg; sfun!(dec; c.clone(), sfun!(nonce; k.clone())))
                    // ),
                    sfun!(eval_cond; sfun!(verify; c.clone(), sfun!(nonce; k.clone()))),
                    sexists!(m!4:msg, r!5:nonce_sort; {
                        let nc = sfun!(enc; m.clone(),  sfun!(nonce; r.clone()), sfun!(nonce; k.clone()));
                        sor!(
                            subt_sk.main(k.clone(), c.clone(), &msg),
                            subt_main.main(nc, c.clone(), &msg) // ,
                            // sfun!(sp; k.clone(), c.clone())
                        )
                    })
                )
            })));
        }
    }
}

fn senc_rand(
    ctx: &mut Ctx,
    enc: &Function,
    dec: &Function,
    verify: &Function,
    fail: &Function,
) -> bool {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let eval_cond = EVAL_COND(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let cond = CONDITION(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();

    // sp

    // all the randomness nonces + some context
    // Err if something else than a nonce is used as randomness or key in enc
    let randomness: Result<Vec<_>, ()> = ctx
        .pbl
        .iter_content()
        .map(|(_, f)| f)
        .flat_map(|f| {
            f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                RichFormula::Var(v) if v.sort == msg || v.sort == nonce_sort => panic!("nope"),
                RichFormula::Var(_) => (None, vec![]),
                RichFormula::Fun(fun, args) if fun == enc => (Some(f), vec![&args[0]]),
                RichFormula::Fun(_, args) => (None, args.iter().collect()),
                _ => (None, vec![]),
            })
        })
        .map(|f| match f {
            RichFormula::Fun(_, args) => {
                if_chain!(
                    if let RichFormula::Fun(f2, r) = &args[1];
                    if let RichFormula::Fun(f1, sk) = &args[2];
                    if f1 == &nonce && f2 == &nonce;
                    then{ Ok((&args[0], &sk[0], &r[0])) }
                    else {
                        println!("err at {}", SmtFormula::from(f));
                        Err(())
                    }
                )
            }
            _ => unreachable!(),
        })
        .collect();

    // if Ok, all the randomness nonces. Thoses should not appear outside of a enc
    // Err if a randomness encrypts two differents messages or is used with two different keys
    let randomness = randomness.and_then(|rands| {
        if rands
            .iter()
            .cartesian_product(rands.iter())
            .all(|((m1, sk1, r1), (m2, sk2, r2))| {
                // println!(
                //     "unifier_check:\n m {} -> {}\n sk {} -> {}\n r {} -> {}",
                //     SmtFormula::from(*m1),
                //     SmtFormula::from(*m2),
                //     SmtFormula::from(*sk1),
                //     SmtFormula::from(*sk2),
                //     SmtFormula::from(*r1),
                //     SmtFormula::from(*r2),
                // );
                if let Some(mgu) = Unifier::mgu(r1, r2) {
                    mgu.does_unify(sk1, sk2) && mgu.does_unify(m1, m2)
                } else {
                    true
                }
            })
        {
            Ok(rands
                .into_iter()
                .map(|(_, _, n)| match n {
                    RichFormula::Fun(fun, _) => fun,
                    _ => unreachable!(),
                })
                .collect_vec())
        } else {
            dbg!("there");
            Err(())
        }
    });

    let ok = match randomness {
        Ok(randomness) => ctx
            .pbl
            .iter_content()
            .map(|(_, f)| f)
            .flat_map(|f| {
                f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                    RichFormula::Fun(fun, _) if randomness.contains(&fun) => {
                        println!("err at {}", fun.name());
                        (Some(()), vec![])
                    }
                    RichFormula::Fun(fun, _) if fun == enc => (None, vec![]),
                    RichFormula::Fun(_, args) => (None, args.iter().collect()),
                    _ => (None, vec![]),
                })
            })
            .next()
            .is_none(),
        Err(_) => false,
    };

    if !ok {
        println!("WARN: int-ctxt is useless")
    }

    // assertions.push(Smt::Assert(sforall!(c!0:msg, k!1:nonce_sort;{
    //     if !ok {
    //         sfun!(sp; k, c)
    //     } else {
    //         snot!(ctx.env(); sfun!(sp; k, c))
    //     }
    // })))
    ok
}
