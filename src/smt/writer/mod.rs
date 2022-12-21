
use std::collections::HashMap;
mod declare;
mod nonce;
mod order;
mod evaluate;

use itertools::{Either, Itertools};

use crate::{
    formula::{
        builtins::{
            functions::{
                EVAL_COND_NAME, EVAL_MSG_NAME, HAPPENS, HAPPENS_NAME, IF_THEN_ELSE,
                IF_THEN_ELSE_NAME, LT_NAME,
            },
            steps::INIT,
            types::{BITSTRING, BOOL, CONDITION, MSG, NONCE, STEP},
        },
        env::Environement,
        formula::{sorts_to_variables, RichFormula, Variable},
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::problem::{
        Problem, QuantifierPContent, CAND_NAME, CEQ_NAME, CFALSE_NAME, CNOT_NAME, COR_NAME,
        CTRUE_NAME,
    },
    smt::smt::RewriteKind,
};

use super::{
    macros::*,
    smt::{Smt, SmtCons, SmtFormula},
};

pub(crate) struct Ctx<'a> {
    pub(crate) ta_funs: Vec<&'a Function>,
    pub(crate) free_funs: Vec<&'a Function>,
    pub(crate) ta_sorts: Vec<&'a Sort>,
    pub(crate) free_sorts: Vec<&'a Sort>,
    pub(crate) pbl: &'a Problem,
}

pub fn problem_to_smt(env: &Environement, mut pbl: Problem) -> Vec<Smt> {
    let Problem {
        steps,
        functions,
        sorts,
        assertions,
        query,
        order,
        lemmas,
        crypto_assumptions,
        quantifiers,
    } = &pbl;

    let mut declarations = Vec::new();
    let mut assertions = Vec::new();

    let (ta_funs, free_funs): (Vec<_>, Vec<_>) = functions.into_iter().partition_map(|(_, f)| {
        if f.is_term_algebra() {
            Either::Left(f)
        } else {
            Either::Right(f)
        }
    });
    let (ta_sorts, free_sorts): (Vec<_>, Vec<_>) = sorts.into_iter().partition_map(|s| {
        if s.is_term_algebra() {
            Either::Left(s)
        } else {
            Either::Right(s)
        }
    });

    let mut ctx = Ctx {
        ta_funs,
        free_funs,
        ta_sorts,
        free_sorts,
        pbl: &pbl,
    };

    // declare sorts and funs
    declare::declare(env, &mut assertions, &mut declarations, &ctx);

    // nonce pseudo ta
    nonce::nonce_pseudo_ta(env, &mut assertions, &mut declarations, &ctx);

    // ordering
    order::ordering(env, &mut assertions, &mut declarations, &ctx);

    // evaluate
    evaluate::evaluate(env, &mut assertions, &mut declarations, &ctx);

    declarations.extend(assertions.into_iter());
    declarations
}



