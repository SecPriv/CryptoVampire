use crate::{
    formula::builtins::{
        functions::{EVAL_MSG, NONCE_MSG},
        types::{MSG, NONCE},
    },
    smt::{
        macros::{seq, sforall, sfun, simplies},
        smt::Smt,
        writer::{
            subterm::{builder::DefaultBuilder, Subterm},
            Ctx,
        },
    },
};

pub(crate) fn generate(assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>, ctx: &mut Ctx) {
    // if ctx.env().no_subterm() {
    //     return;
    // }

    let eval_msg = EVAL_MSG(ctx.env()).clone();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();

    let subt_main = Subterm::new_and_init(
        assertions,
        declarations,
        ctx,
        "sbt$nonce_main".to_owned(),
        nonce_sort.clone(),
        [],
        Default::default(),
        DefaultBuilder(),
    );

    assertions.push(Smt::Assert(sforall!(n!0:nonce_sort, m!1:msg;{
        simplies!(ctx.env();
            seq!(sfun!(eval_msg; sfun!(nonce; n.clone())), sfun!(eval_msg; m.clone())),
            subt_main.f(ctx, n.clone(), m.clone(), &msg)
        )
    })))
}
