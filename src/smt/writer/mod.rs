mod declare;
mod evaluate;
mod nonce;
mod order;
pub(crate) mod subterm;

use itertools::{Either, Itertools};

use crate::{
    formula::{env::Environement, function::Function, sort::Sort},
    problem::problem::Problem,
};

use super::smt::Smt;

pub(crate) struct Ctx {
    pub(crate) ta_funs: Vec<Function>,
    pub(crate) free_funs: Vec<Function>,
    pub(crate) ta_sorts: Vec<Sort>,
    pub(crate) free_sorts: Vec< Sort>,
    pub(crate) pbl: Problem,
}

impl Ctx {
    pub(crate) fn env(&self) -> &Environement {
        &self.pbl.env
    }
    pub(crate) fn env_mut(&mut self) -> &mut Environement {
        &mut self.pbl.env
    }
}

pub fn problem_to_smt(mut pbl: Problem) -> Vec<Smt> {
    let mut declarations = Vec::new();
    let mut assertions = Vec::new();

    let ta_funs;
    let free_funs;
    let ta_sorts;
    let free_sorts;

    {
        let Problem {
            steps: _,
            env,
            assertions: _,
            query: _,
            order: _,
            lemmas: _,
            crypto_assumptions: _,
            quantifiers: _,
        } = &pbl;

         (ta_funs, free_funs) = env.get_functions_iter().cloned().partition_map(|f| {
            if f.is_term_algebra() {
                Either::Left(f)
            } else {
                Either::Right(f)
            }
        });
         (ta_sorts, free_sorts) = env.get_sort_iter().cloned().partition_map(|s| {
            if s.is_term_algebra() {
                Either::Left(s)
            } else {
                Either::Right(s)
            }
        });
    }

    let mut ctx = Ctx {
        ta_funs,
        free_funs,
        ta_sorts,
        free_sorts,
        pbl: pbl,
    };

    // declare sorts and funs
    declare::declare(ctx.env(), &mut assertions, &mut declarations, &ctx);

    // nonce pseudo ta
    nonce::nonce_pseudo_ta(ctx.env(), &mut assertions, &mut declarations, &ctx);

    // ordering
    order::ordering(ctx.env(), &mut assertions, &mut declarations, &ctx);

    // evaluate
    evaluate::evaluate(ctx.env(), &mut assertions, &mut declarations, &ctx);

    // crypto
    {
        let tmp = ctx.pbl.crypto_assumptions.iter().cloned().collect_vec();
        for c in tmp {
            c.generate_smt(&mut assertions, &mut declarations, &mut ctx);
        }
    }

    // order
    assertions.extend(ctx.pbl.order.iter().map(|f| Smt::Assert(f.into())));

    // query
    assertions.push(Smt::AssertNot((&ctx.pbl.query).into()));

    declarations.extend(assertions.into_iter());
    declarations.push(Smt::CheckSat);
    declarations
}
