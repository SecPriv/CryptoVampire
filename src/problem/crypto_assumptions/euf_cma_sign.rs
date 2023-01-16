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