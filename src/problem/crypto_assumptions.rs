use crate::{
    formula::{
        builtins::{
            functions::{EVAL_MSG, NONCE_MSG},
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

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption {
    EufCmaHash(Function),
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
                generate_smt_euf_sma_hash( assertions, declarations, ctx, f)
            }
            CryptoAssumption::Nonce => generate_smt_nonce(assertions, declarations, ctx),
        }
    }
}

fn generate_smt_nonce(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
) {
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

fn generate_smt_euf_sma_hash(
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
                        s.f(k.clone(), k2.clone(), &nonce_sort)
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
        todo!()
    }
}
