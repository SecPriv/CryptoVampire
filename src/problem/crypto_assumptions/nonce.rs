use std::convert::identity;

use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::problem::crypto_assumptions::aux;
use crate::smt::get_eval_msg;
use crate::{
    formula::{
        builtins::{
            functions::{ INPUT, LT, NONCE_MSG},
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
pub(crate) fn generate(assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>, ctx: &mut Ctx) {
    // if ctx.env().no_subterm() {
    //     return;
    // }

    let eval_msg = get_eval_msg(ctx.env());
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
            seq!(eval_msg( sfun!(nonce; n.clone())), eval_msg( m.clone())),
            subt_main.main(n.clone(), m.clone(), &msg)
        )
    })))
}
