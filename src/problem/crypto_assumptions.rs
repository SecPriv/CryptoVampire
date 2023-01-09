use crate::{
    formula::{
        builtins::{
            functions::{EVAL_MSG, NONCE_MSG},
            types::{MSG, NONCE, BOOL},
        },
        function::{FFlags, Function},
    },
    smt::{
        macros::{sand, seq, sexists, sforall, sfun, simplies, site, snot, sor, srewrite, sneq},
        smt::{RewriteKind, Smt},
        writer::{subterm::generate_subterm, Ctx},
    },
};

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption {
    EufCmaHash(Function),
    EufCmaSign {
        sign: Function,
        verify: Function,
        pk: Function,
        fail: Function,
    },
    IntCtxtSenc {
        enc: Function,
        dec: Function,
        fail: Function,
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
            CryptoAssumption::EufCmaHash(f) => {
                generate_smt_euf_cma_hash(assertions, declarations, ctx, f)
            }
            CryptoAssumption::Nonce => generate_smt_nonce(assertions, declarations, ctx),
            CryptoAssumption::EufCmaSign {
                sign,
                verify,
                pk,
                fail,
            } => generate_smt_euf_cma_sign(assertions, declarations, ctx, sign, verify, pk, fail),
            CryptoAssumption::IntCtxtSenc { enc, dec, fail } => {
                generate_smt_int_ctxt_senc(assertions, declarations, ctx, enc, dec, fail)
            }
        }
    }
}

fn generate_smt_int_ctxt_senc(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    enc: &Function,
    dec: &Function,
    fail: &Function,
) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();

    let subt_main = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_ctxt_main",
        &msg,
        vec![],
    );
    let subt_sec = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_ctxt_sec",
        &nonce_sort,
        vec![enc, dec],
    );
    let subt_rd = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_ctxt_rd",
        &nonce_sort,
        vec![enc],
    );

    for s in subt_sec.iter() {
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
    assertions.push(Smt::Assert(sforall!(m!0:msg, r!1:nonce_sort, sk!2:nonce_sort; {
        let r = sfun!(nonce; r);
        let sk = sfun!(nonce; sk);
        seq!(
            sfun!(eval_msg; sfun!(dec; sfun!(enc; m.clone(), r, sk.clone()), sk)),
            sfun!(eval_msg; m)
        )
    })));

    let sp = Function::new_with_flag(
        "sp$int_ctxt",
        vec![nonce_sort.clone(), msg.clone()],
        BOOL(ctx.env()).clone(),
        FFlags::empty(),
    );
    declarations.push(Smt::DeclareFun(sp.clone()));
    assertions.push(Smt::Assert(sforall!(c!0:msg, k!1:nonce_sort, r!2:msg, m!3:msg; {
        simplies!(ctx.env();
            sand!(
                sfun!(sp; k.clone(), c.clone()),
                subt_main.main(sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg)
            ),
            sor!(
                sforall!(n!4:nonce_sort; {sneq!(r.clone(), sfun!(nonce; n))}),
                sexists!(m2!4:msg; {
                    sand!(
                        subt_main.main(sfun!(enc; m2.clone(), r.clone(), sfun!(nonce; k.clone())), c.clone(), &msg),
                        sneq!(m2, m.clone())
                    )
                }),
                sexists!(n!4:nonce_sort; {sand!(
                    seq!(r.clone(), sfun!(nonce; n.clone())),
                    subt_rd.main(n.clone(), c.clone(), &msg)
                )})
            )
            
        )
    })));
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
                sneq!(
                    sfun!(eval_msg; sfun!(fail; )),
                    sfun!(eval_msg; sfun!(dec; c.clone(), sfun!(nonce; k.clone())))
                )
            } -> {
                let m = sfun!(sk_m; c.clone(), k.clone());
                let r = sfun!(sk_r; c.clone(), k.clone());
                let nc = sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone()));
                sor!(
                    subt_sec.main(k.clone(), c.clone(), &msg),
                    subt_main.main(nc, c.clone(), &msg),
                    sfun!(sp; k.clone(), c.clone())
                )
            }
        ));
    } else {
        assertions.push(Smt::Assert(sforall!(c!2:msg, k!3:nonce_sort;{ 
            simplies!(ctx.env(); 
                sneq!(
                    sfun!(eval_msg; sfun!(fail; )),
                    sfun!(eval_msg; sfun!(dec; c.clone(), sfun!(nonce; k.clone())))
                ), 
                sexists!(m!4:msg, r!5:nonce_sort; {
                    let nc = sfun!(enc; m.clone(), r.clone(), sfun!(nonce; k.clone()));
                    sor!(
                        subt_sec.main(k.clone(), c.clone(), &msg),
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
    hash: &Function,
) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();

    let subt_main = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_main",
        &msg,
        vec![],
    );
    let subt_sec = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_sec",
        &nonce_sort,
        vec![hash],
    );

    for s in subt_sec.iter() {
        assertions.push(Smt::Assert(sforall!(k!0:nonce_sort, m!1:msg, k2!2:msg; {
            simplies!(ctx.env();
                s.f(k.clone(), sfun!(hash; m.clone(), k2.clone()), &msg),
                site!(
                    seq!(k2.clone(), sfun!(nonce; k.clone())),
                    s.f(k.clone(), m.clone(), &msg),
                    sor!(
                        s.f(k.clone(), m.clone(), &msg),
                        s.f(k.clone(), k2.clone(), &msg)
                    )
                )
            )
        })))
    }

    if ctx.env().crypto_rewrite() {
        let sk = Function::new_with_flag(
            "sk$u$euf_cma_hash",
            vec![msg.clone(), msg.clone(), nonce_sort.clone()],
            msg.clone(),
            FFlags::SKOLEM,
        );
        let asser = srewrite!(
                RewriteKind::Bool; s!1:msg, k!2:nonce_sort, m!3:msg;
                {
                    seq!(
                        sfun!(eval_msg; s.clone()),
                        sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                    )
                } -> {
                    let u = sfun!(sk; s.clone(), m.clone(), k.clone());
                    let h = sfun!(hash; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.main(h.clone(), s.clone(), &msg),
                            subt_main.main(h.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; h.clone()), sfun!(eval_msg; s.clone()))
                    )
                }
        );

        declarations.push(Smt::DeclareFun(sk));
        assertions.push(asser);
    } else {
        let asser = sforall!(s!1:msg, k!2:nonce_sort, m!3:msg;{
                simplies!(ctx.env();
                    seq!(
                        sfun!(eval_msg; s.clone()),
                        sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                    )
                ,
                    sexists!(u!4:msg; {
                    let h = sfun!(hash; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.main(h.clone(), s.clone(), &msg),
                            subt_main.main(h.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; h.clone()), sfun!(eval_msg; s.clone()))
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
    pk: &Function,
    fail: &Function,
) {
    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();

    let subt_main = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_sign_main",
        &msg,
        vec![],
    );
    let subt_sec = generate_subterm(
        assertions,
        declarations,
        ctx,
        "sbt$euf_sign_sec",
        &nonce_sort,
        vec![sign, pk],
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
                s.f(sk.clone(), sfun!(pk;  mpk.clone()), &msg),
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
        assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg; {
            seq!(
                sfun!(eval_msg; sfun!(verify; sfun!(sign; m.clone(), sfun!(nonce; sk.clone())), sfun!(pk; sfun!(nonce; sk.clone())))),
                sfun!(eval_msg; m)
            )
        })))
    }

    if ctx.env().crypto_rewrite() {
        let sk = Function::new_with_flag(
            "sk$u$euf_cma_sign",
            vec![msg.clone(), msg.clone(), nonce_sort.clone()],
            msg.clone(),
            FFlags::SKOLEM,
        );
        let asser = srewrite!(
                RewriteKind::Bool; s!1:msg, k!2:nonce_sort, m!3:msg;
                {
                    sand!(
                        seq!(
                            sfun!(eval_msg; s.clone()),
                            sfun!(eval_msg; sfun!(verify; m.clone(), sfun!(pk; sfun!(nonce; k.clone()))))
                        ),
                        snot!(ctx.env(); seq!(
                            sfun!(eval_msg; sfun!(fail; )),
                            sfun!(eval_msg; s.clone())
                        ))
                    )
                } -> {
                    let u = sfun!(sk; s.clone(), m.clone(), k.clone());
                    let sig = sfun!(sign; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.main(sig.clone(), s.clone(), &msg),
                            subt_main.main(sig.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; sig.clone()), sfun!(eval_msg; s.clone()))
                    )
                }
        );

        declarations.push(Smt::DeclareFun(sk));
        assertions.push(asser);
    } else {
        let asser = sforall!(s!1:msg, k!2:nonce_sort, m!3:msg;{
                simplies!(ctx.env();
                    sand!(
                        seq!(
                            sfun!(eval_msg; s.clone()),
                            sfun!(eval_msg; sfun!(verify; m.clone(), sfun!(pk; sfun!(nonce; k.clone()))))
                        ),
                        snot!(ctx.env(); seq!(
                            sfun!(eval_msg; sfun!(fail; )),
                            sfun!(eval_msg; s.clone())
                        ))
                    )
                ,
                    sexists!(u!4:msg; {
                    let sig = sfun!(sign; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.main(sig.clone(), s.clone(), &msg),
                            subt_main.main(sig.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), m.clone(), &msg),
                            subt_sec.main(k.clone(), s.clone(), &msg)
                        ),
                        seq!(sfun!(eval_msg; sig.clone()), sfun!(eval_msg; s.clone()))
                    )})
                )}
        );
        assertions.push(Smt::Assert(asser));
    }
}
