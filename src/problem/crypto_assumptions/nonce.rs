use crate::{
    formula::{
        builtins::{
            functions::NONCE_MSG,
            types::{MSG, NONCE},
        },
        formula_user::FormulaUser,
        utils::Evaluator,
    },
    smt::{
        smt::{Smt, SmtFormula},
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

    // let eval_msg = get_eval_msg(ctx.env());
    let evaluator = Evaluator::new(ctx.env()).unwrap();
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

    // assertions.push(Smt::Assert(sforall!(n!0:nonce_sort, m!1:msg;{
    //     simplies!(ctx.env();
    //         seq!(sfun!(eval_msg; sfun!(nonce; n.clone())), sfun!(eval_msg; m.clone())),
    //         subt_main.f(ctx, n.clone(), m.clone(), &msg)
    //     )
    // })))

    assertions.push(Smt::Assert(ctx.forallff(
        [(0, &nonce_sort), (1, &msg)],
        |[n, m]: [SmtFormula; 2]| {
            ctx.impliesf(
                ctx.eqf(
                    evaluator.msg(ctx, nonce.cf(ctx, [n.clone()])),
                    evaluator.msg(ctx, m.clone()),
                ),
                subt_main.f(ctx, n, m, &msg),
            )
        },
    )))
}
