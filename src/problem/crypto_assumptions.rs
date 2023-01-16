use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::{
    formula::{
        builtins::{
            functions::{EVAL_COND, EVAL_MSG, NONCE_MSG},
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
        macros::{sand, seq, sexists, sforall, sfun, simplies, site, sneq, snot, sor, srewrite},
        smt::{RewriteKind, Smt, SmtFormula},
        writer::{
            subterm::{default_f, generate_subterm, Subterm},
            Ctx,
        },
    },
};

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption {
    EufCmaMac {
        /// mac(Message, Key) -> Signature
        mac: Function,
        /// verify(Signature, Message, Key) -> bool
        verify: Function,
    },
    EufCmaSign {
        /// sign(Message, Key) -> Signature
        sign: Function,
        /// verify(Signature, Message, vKey) -> bool
        verify: Function,
        pk: Function,
    },
    IntCtxtSenc {
        enc: Function,
        dec: Function,
        fail: Function,
        verify: Function,
    },
    Nonce,
}

impl CryptoAssumption {
    pub(crate) fn generate_smt(
        &self,
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &mut Ctx,
    ) {
        match self {
            CryptoAssumption::EufCmaMac { mac, verify } => {
                generate_smt_euf_cma_hash(assertions, declarations, ctx, mac, verify)
            }
            CryptoAssumption::Nonce => generate_smt_nonce(assertions, declarations, ctx),
            CryptoAssumption::EufCmaSign { sign, verify, pk } => {
                generate_smt_euf_cma_sign(assertions, declarations, ctx, sign, verify, pk)
            }
            CryptoAssumption::IntCtxtSenc {
                enc,
                dec,
                verify,
                fail,
            } => generate_smt_int_ctxt_senc(assertions, declarations, ctx, enc, dec, verify, fail),
        }
    }
}

fn aux(m: &SmtFormula, f: &RichFormula) -> SmtFormula {
    seq!(m.clone(), SmtFormula::from(f))
}
fn generate_smt_int_ctxt_senc(
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
    assertions.push(Smt::Assert(
        sforall!(m!0:msg, r!1:nonce_sort, sk!2:nonce_sort; {
            let r = sfun!(nonce; r);
            let sk = sfun!(nonce; sk);
            seq!(
                sfun!(eval_msg; sfun!(dec; sfun!(enc; m.clone(), r, sk.clone()), sk)),
                sfun!(eval_msg; m)
            )
        }),
    ));

    assertions.push(Smt::Assert(
        sforall!(m!0:msg, r!1:nonce_sort, sk!2:nonce_sort; {
            let r = sfun!(nonce; r);
            let sk = sfun!(nonce; sk);
            sfun!(eval_cond; sfun!(verify; sfun!(enc; m.clone(), r, sk.clone()), sk.clone()))
        }),
    ));

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

    let sp = Function::new_with_flag(
        "sp$int_ctxt",
        vec![nonce_sort.clone(), msg.clone()],
        BOOL(ctx.env()).clone(),
        FFlags::empty(),
    );
    declarations.push(Smt::DeclareFun(sp.clone()));

    // let's ignore this for now
    if false {
        assertions.push(Smt::Assert(sforall!(c!0:msg, k!1:nonce_sort; {
            simplies!(ctx.env();
                // sand!(
                //     sfun!(sp; k.clone(), c.clone()),
                //     subt_main.main(sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg)
                // ),
                sfun!(sp; k.clone(), c.clone()),
                sexists!( r!2:msg, m!3:msg;{
                    sand!(
                        subt_main.main(sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg),
                        sor!(
                            sforall!(n!4:nonce_sort; {sneq!(r.clone(), sfun!(nonce; n))}),
                            sexists!(m2!4:msg, k2!5:msg; {
                                sand!(
                                    subt_main.main(sfun!(enc; m2.clone(), r.clone(), k2.clone()), c.clone(), &msg),
                                    sneq!(m2, m.clone()),
                                    sneq!(k2,  sfun!(nonce; k.clone()))
                                )
                            }),
                            sexists!(n!4:nonce_sort; {sand!(
                                seq!(r.clone(), sfun!(nonce; n.clone())),
                                subt_rd.main(n.clone(), c.clone(), &msg)
                            )})
                        )
                    )
                })
            )
        })));
    }

    {
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
                        if let RichFormula::Fun(f1, sk) = &args[1];
                        if let RichFormula::Fun(f2, n) = &args[2];
                        if f1 == &nonce && f2 == &nonce;
                        then{ Ok((&args[0], &sk[0], &n[0])) }
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
        // Err if a randomness encrypts two different messages or is used with two different keys
        let randomness =
            randomness.and_then(|rands| {
                if rands.iter().cartesian_product(rands.iter()).all(
                    |((m1, sk1, n1), (m2, sk2, n2))| {
                        if let Some(mgu) = Unifier::mgu(n1, n2) {
                            mgu.does_unify(sk1, sk2) && mgu.does_unify(m1, m2)
                        } else {
                            println!("err at {} -> {}", SmtFormula::from(*m1), SmtFormula::from(*m2));
                            println!("or at {} -> {}", SmtFormula::from(*sk1), SmtFormula::from(*sk2));
                            false
                        }
                    },
                ) {
                    Ok(rands
                        .into_iter()
                        .map(|(_, _, n)| match n {
                            RichFormula::Fun(fun, _) => fun,
                            _ => unreachable!(),
                        })
                        .collect_vec())
                } else {
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
                        },
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

        assertions.push(Smt::Assert(sforall!(c!0:msg, k!1:nonce_sort;{
            if !ok {
                sfun!(sp; c, k)
            } else {
                snot!(ctx.env(); sfun!(sp; c, k))
            }
        })))
    }

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
                sfun!(eval_cond; sfun!(verify; c.clone(), k.clone()))
            } -> {
                let m = sfun!(sk_m; c.clone(), k.clone());
                let r = sfun!(sk_r; c.clone(), k.clone());
                let nc = sfun!(enc; m.clone(), sfun!(nonce; r.clone()), sfun!(nonce; k.clone()));
                sor!(
                    subt_sk.main(k.clone(), c.clone(), &msg),
                    subt_main.main(nc, c.clone(), &msg),
                    sfun!(sp; k.clone(), c.clone())
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
                sfun!(eval_cond; sfun!(verify; c.clone(), k.clone())),
                sexists!(m!4:msg, r!5:nonce_sort; {
                    let nc = sfun!(enc; m.clone(),  sfun!(nonce; r.clone()), sfun!(nonce; k.clone()));
                    sor!(
                        subt_sk.main(k.clone(), c.clone(), &msg),
                        subt_main.main(nc, c.clone(), &msg),
                        sfun!(sp; k.clone(), c.clone())
                    )
                })
            )
        })));
    }
}

fn generate_smt_nonce(assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>, ctx: &mut Ctx) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();

    let subt_main = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$nonce_main",
        &nonce_sort,
        vec![],
        default_f(),
    );

    assertions.push(Smt::Assert(sforall!(n!0:nonce_sort, m!1:msg;{
        simplies!(ctx.env();
            seq!(sfun!(eval_msg; sfun!(nonce; n.clone())), sfun!(eval_msg; m.clone())),
            subt_main.main(n.clone(), m.clone(), &msg)
        )
    })))
}

fn generate_smt_euf_cma_hash(
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
    assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg; {
                sfun!(eval_cond; sfun!(verify; sfun!(mac; m.clone(), sfun!(nonce; sk.clone())), m.clone(),  sfun!(nonce; sk.clone())))
        })));

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
                            subt_main.main(h.clone(), s.clone(), &msg),
                            subt_main.main(h.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
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
                            subt_main.main(h.clone(), s.clone(), &msg),
                            subt_main.main(h.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; m.clone()), sfun!(eval_msg; u.clone()))
                    )})
                )}
        );
        assertions.push(Smt::Assert(asser));
    }
}

fn generate_smt_euf_cma_sign(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    sign: &Function,
    verify: &Function,
    vk: &Function,
) {
    let eval_cond = EVAL_COND(ctx.env()).clone();
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();

    let subt_main = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_sign",
        &msg,
        vec![],
        default_f(),
    );
    let subt_sec = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_sign_sec",
        &nonce_sort,
        vec![sign, vk],
        |_, m, _, _, f| match f {
            RichFormula::Var(v) if v.sort == nonce_sort => (Some(aux(m, f)), vec![]),
            RichFormula::Fun(fun, args) if fun == sign => {
                let mut todo = Vec::with_capacity(2);
                todo.push(&args[0]);
                if_chain!(
                    if let RichFormula::Fun(fun2, _) = &args[2];
                    if fun2 == &nonce;
                    then {}
                    else {
                        todo.push(&args[1])
                    }
                );
                (None, todo)
            }
            RichFormula::Fun(fun, args) if fun == vk => {
                let mut todo = Vec::with_capacity(1);
                if_chain!(
                    if let RichFormula::Fun(fun2, _) = &args[0];
                    if fun2 == &nonce;
                    then {}
                    else {
                        todo.push(&args[0])
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
                s.f(k.clone(), sfun!(sign; m.clone(), k2.clone()), &msg),
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
        assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, mpk!2:msg; {
            simplies!(ctx.env();
                s.f(sk.clone(), sfun!(vk;  mpk.clone()), &msg),
                // site!(
                //     seq!(mpk.clone(), sfun!(nonce; sk.clone())),
                //     s.f(sk.clone(), m.clone(), &msg),
                //     sor!(
                //         s.f(sk.clone(), m, &msg),
                //         s.f(sk, mpk, &msg)
                //     )
                // )
                sor!(
                    seq!(mpk.clone(), sfun!(nonce; sk.clone())),
                    s.f(sk, mpk, &msg)
                )
            )
        })));
    }
    assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg; {
                sfun!(eval_cond; sfun!(verify; sfun!(sign; m.clone(), sfun!(nonce; sk.clone())), m.clone(), sfun!(vk; sfun!(nonce; sk.clone()))))
        })));

    if ctx.env().crypto_rewrite() {
        let skolem = Function::new_with_flag(
            "sk$u$euf_cma_sign",
            vec![msg.clone(), msg.clone(), nonce_sort.clone()],
            msg.clone(),
            FFlags::SKOLEM,
        );
        let asser = srewrite!(
                RewriteKind::Bool; s!1:msg, sk!2:nonce_sort, m!3:msg;
                {
                    sfun!(eval_cond; sfun!(verify; s.clone(), sfun!(vk; sfun!(nonce; sk.clone()))))
                } -> {
                    let u = sfun!(skolem; s.clone(), m.clone(), sk.clone());
                    let sig = sfun!(sign; u.clone(), sfun!(nonce; sk.clone()));
                    sand!(
                        sor!(
                            subt_main.main(sig.clone(), s.clone(), &msg),
                            subt_main.main(sig.clone(), m.clone(), &msg),
                            subt_sec.main(sk.clone(), m.clone(), &msg),
                            subt_sec.main(sk.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; m.clone()), sfun!(eval_msg; u.clone()))
                    )
                }
        );

        declarations.push(Smt::DeclareFun(skolem));
        assertions.push(asser);
    } else {
        let asser = sforall!(s!1:msg, sk!2:nonce_sort, m!3:msg;{
                simplies!(ctx.env();
                    // sand!(
                    //     seq!(
                    //         sfun!(eval_msg; s.clone()),
                    //         sfun!(eval_msg; sfun!(verify; m.clone(), sfun!(vk; sfun!(nonce; sk.clone()))))
                    //     ),
                    //     snot!(ctx.env(); seq!(
                    //         sfun!(eval_msg; sfun!(fail; )),
                    //         sfun!(eval_msg; s.clone())
                    //     ))
                    // )
                    sfun!(eval_cond; sfun!(verify; s.clone(), sfun!(vk; sfun!(nonce; sk.clone()))))
                ,
                    sexists!(u!4:msg; {
                    let sig = sfun!(sign; u.clone(), sfun!(nonce; sk.clone()));
                    sand!(
                        sor!(
                            subt_main.main(sig.clone(), s.clone(), &msg),
                            subt_main.main(sig.clone(), m.clone(), &msg),
                            subt_sec.main(sk.clone(), m.clone(), &msg),
                            subt_sec.main(sk.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; sig.clone()), sfun!(eval_msg; s.clone()))
                    )})
                )}
        );
        assertions.push(Smt::Assert(asser));
    }
}
