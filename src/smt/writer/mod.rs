mod declare;
mod evaluate;
mod nonce;
mod order;
pub(crate) mod subterm;

use itertools::{Either, Itertools};

use crate::{
    formula::{env::Environement, formula::RichFormula, function::Function, sort::Sort},
    problem::problem::Problem,
};

use super::smt::Smt;

pub(crate) struct Ctx {
    pub(crate) ta_funs: Vec<Function>,
    pub(crate) free_funs: Vec<Function>,
    pub(crate) ta_sorts: Vec<Sort>,
    pub(crate) free_sorts: Vec<Sort>,
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

pub fn problem_to_smt(pbl: Problem) -> Vec<Smt> {
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

    if ctx.env().skolemnise() {
        skolemnise(&mut ctx, &mut assertions, &mut declarations);
    }

    declarations.extend(assertions.into_iter());
    declarations.push(Smt::CheckSat);
    declarations
}

fn skolemnise(ctx: &mut Ctx, assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>) {
    for s in assertions.iter_mut() {
        match s {
            Smt::Assert(f) | Smt::AssertTh(f) => take_mut::take(f, |f| {
                let (f, sk) = f.skolemnise(ctx.env_mut(), false, &[]);
                declarations.extend(sk.into_iter().map(|fun| Smt::DeclareFun(fun)));
                f
            }),
            Smt::AssertNot(f) => take_mut::take(f, |f| {
                let (f, sk) = f.skolemnise(ctx.env_mut(), true, &[]);
                declarations.extend(sk.into_iter().map(|fun| Smt::DeclareFun(fun)));
                f
            }),
            _ => continue,
        }
    }
}

pub fn problem_smts_with_lemma(pbl: Problem) -> impl Iterator<Item = Vec<Smt>> {
    let Problem {
        steps,
        env,
        assertions,
        query,
        order,
        mut lemmas,
        crypto_assumptions,
        quantifiers,
    } = pbl;

    // the last lemma is the query
    lemmas.push(query);

    let mut verified_lemmas: Vec<RichFormula> = Vec::new();

    lemmas.into_iter().map(move |lemma| {
        // this hurts a little ^^'
        let pbl = Problem {
            steps: steps.clone(),
            env: env.clone(),
            assertions: assertions.clone(),
            query: lemma.clone(),
            order: order.clone(),
            lemmas: vec![],
            crypto_assumptions: crypto_assumptions.clone(),
            quantifiers: quantifiers.clone(),
        };

        let mut smt = problem_to_smt(pbl);
        smt.extend(
            verified_lemmas
                .iter()
                .map(|old_lemma| Smt::Assert(old_lemma.clone().into())),
        );

        verified_lemmas.push(lemma);

        smt
    })
}
