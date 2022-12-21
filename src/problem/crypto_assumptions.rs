use crate::{
    formula::{
        builtins::{
            functions::{EVAL_MSG_NAME, NONCE_MSG_NAME},
            types::{MSG, NONCE},
        },
        env::Environement,
        function::{FFlags, Function},
    },
    smt::{
        macros::{sand, seq, sforall, sfun, simplies, site, sor, srewrite},
        smt::{RewriteKind, Smt},
        writer::{subterm::generate_subterm, Ctx},
    },
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CryptoAssumption {
    EufCmaHash(Function),
    Nonce,
}

impl CryptoAssumption {
    pub(crate) fn generate_smt(
        &self,
        env: &Environement,
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &Ctx<'_>,
    ) {
        match self {
            CryptoAssumption::EufCmaHash(f) => {
                generate_smt_euf_sma_hash(env, assertions, declarations, ctx, f)
            }
            CryptoAssumption::Nonce => generate_smt_nonce(env, assertions, declarations, ctx),
        }
    }
}

fn generate_smt_nonce(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let eval_msg = ctx.pbl.functions.get(EVAL_MSG_NAME).unwrap();
    let nonce = ctx.pbl.functions.get(NONCE_MSG_NAME).unwrap();

    let subt_main = generate_subterm(
        env,
        assertions,
        declarations,
        ctx,
        "sbt$nonce_main",
        &NONCE,
        vec![],
    );

    assertions.push(Smt::Assert(sforall!(n!0:NONCE, m!1:MSG;{
        simplies!(
            seq!(sfun!(eval_msg; sfun!(nonce; n.clone())), sfun!(eval_msg; m.clone())),
            subt_main.main(n.clone(), m.clone())
        )
    })))
}

fn generate_smt_euf_sma_hash(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
    hash: &Function,
) {
    let eval_msg = ctx.pbl.functions.get(EVAL_MSG_NAME).unwrap();
    let nonce = ctx.pbl.functions.get(NONCE_MSG_NAME).unwrap();

    let subt_main = generate_subterm(
        env,
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_main",
        &MSG,
        vec![],
    );
    let subt_sec = generate_subterm(
        env,
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_sec",
        &NONCE,
        vec![hash],
    );

    for s in subt_sec.iter() {
        assertions.push(Smt::Assert(sforall!(k!0:NONCE, m!1:MSG, k2!2:MSG; {
            simplies!(
                s.f(k.clone(), sfun!(hash; m.clone(), k2.clone())),
                site!(
                    seq!(k2.clone(), sfun!(nonce; k.clone())),
                    s.f(k.clone(), m.clone()),
                    sor!(
                        s.f(k.clone(), m.clone()),
                        s.f(k.clone(), k2.clone())
                    )
                )
            )
        })))
    }

    if env.crypto_rewrite {
        let sk = Function::new_with_flag(
            "sk$u$euf_cma_hash",
            vec![MSG.clone(), MSG.clone(), NONCE.clone()],
            MSG.clone(),
            FFlags::SKOLEM,
        );
        let asser = srewrite!(
                RewriteKind::Bool; s!1:MSG, k!2:NONCE, m!3:MSG;
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
                            subt_main.main(h.clone(), s.clone()),
                            subt_main.main(h.clone(), m.clone()),
                            subt_sec.main(k.clone(), m.clone()),
                            subt_sec.main(k.clone(), s.clone())
                        ),
                        seq!(sfun!(eval_msg; h.clone()), sfun!(eval_msg; s.clone()))
                    )
                }
        );

        declarations.push(Smt::DeclareFun(sk));
        assertions.push(asser);
    } else {
        todo!()
    }
}
