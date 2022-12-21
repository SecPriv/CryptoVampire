mod declare;
mod evaluate;
mod nonce;
mod order;

use itertools::{Either, Itertools};

use crate::{
    formula::{env::Environement, function::Function, sort::Sort},
    problem::problem::Problem,
};

use super::smt::Smt;

pub(crate) struct Ctx<'a> {
    pub(crate) ta_funs: Vec<&'a Function>,
    pub(crate) free_funs: Vec<&'a Function>,
    pub(crate) ta_sorts: Vec<&'a Sort>,
    pub(crate) free_sorts: Vec<&'a Sort>,
    pub(crate) pbl: &'a Problem,
}

pub fn problem_to_smt(env: &Environement, pbl: Problem) -> Vec<Smt> {
    let Problem {
        steps: _,
        functions,
        sorts,
        assertions: _,
        query: _,
        order: _,
        lemmas: _,
        crypto_assumptions: _,
        quantifiers: _,
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

    let ctx = Ctx {
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
