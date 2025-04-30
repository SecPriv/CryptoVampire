mod declare;
mod evaluate;
mod nonce;
mod order;
pub(crate) mod subterm;

use itertools::{Either, Itertools};

use crate::{
    formula::{
        builtins::{
            functions::{EVAL_COND_NAME, EVAL_MSG_NAME, NONCE_MSG},
            types::NONCE,
        },
        env::Environement,
        formula_user::HasShortcut,
        function::Function,
        sort::Sort,
    },
    problem::{cell_dependancies::graph::DependancyGraph, problem::Problem},
    smt::{
        macros::{seq, sforall, sfun},
        smt::SmtFormula,
    },
};

use super::{
    macros::{simplies, snot},
    smt::Smt,
};

pub struct Ctx {
    pub ta_funs: Vec<Function>,
    pub free_funs: Vec<Function>,
    pub ta_sorts: Vec<Sort>,
    pub free_sorts: Vec<Sort>,
    pub pbl: Problem,
}

impl Ctx {
    pub(crate) fn env(&self) -> &Environement {
        &self.pbl.env
    }
    pub(crate) fn env_mut(&mut self) -> &mut Environement {
        &mut self.pbl.env
    }
}

impl HasShortcut for Ctx {
    fn get_function_shortcut(&self) -> &crate::formula::formula_user::FunctionShortcuter {
        self.env().get_function_shortcut()
    }
}

pub fn problem_to_smt(pbl: Problem) -> Vec<Smt> {
    let mut declarations = vec![
        Smt::SetOption("produce-proofs".to_owned(), "true".to_owned()),
        Smt::SetLogic("ALL".to_owned()),
    ];
    let mut assertions = Vec::new();

    let ta_funs;
    let free_funs;
    let ta_sorts;
    let free_sorts;

    {
        let Problem {
            steps: _,
            memory_cells: _,
            env,
            assertions: _,
            query: _,
            order: _,
            lemmas: _,
            crypto_assumptions: _,
            quantifiers: _,
        } = &pbl;

        (ta_funs, free_funs) = env.get_functions_iter().cloned().partition_map(|f| {
            // dbg!(&f);
            if f.is_term_algebra() && f.get_output_sort().is_term_algebra() {
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
        pbl,
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

        if ctx.env().no_ta() {
            let nonce_sort = NONCE(ctx.env());
            let nonce = NONCE_MSG(ctx.env());

            assertions.push(Smt::Assert(sforall!(n1!1:nonce_sort, n2!2:nonce_sort; {
                simplies!(ctx.env();
                    seq!(sfun!(nonce; n1), sfun!(nonce; n2)),
                    seq!(n1, n2)
                )
            })))
        }
    }

    // order
    assertions.extend(ctx.pbl.order.iter().map(|f| Smt::Assert(f.into())));

    // query
    assertions.push({
        let query = (&ctx.pbl.query).into();
        if ctx.env().cvc5() {
            Smt::Assert(snot!(ctx.env(); query))
        } else {
            Smt::AssertNot(query)
        }
    });

    if ctx.env().no_ta() {
        remove_evals(&ctx, &mut assertions)
    }

    if ctx.env().skolemnise() {
        skolemnise(&mut ctx, &mut assertions, &mut declarations);
    }

    declarations.extend(assertions.into_iter());
    declarations.push(Smt::CheckSat);
    declarations.push(Smt::GetProof);
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

fn remove_evals(ctx: &Ctx, assertions: &mut Vec<Smt>) {
    struct Db {
        m: Function,
        c: Function,
    }

    let eval = {
        let env = ctx.env();
        Db {
            m: env.get_f(EVAL_MSG_NAME).unwrap().clone(),
            c: env.get_f(EVAL_COND_NAME).unwrap().clone(),
        }
    };

    fn aux(f: &mut SmtFormula, eval: &Db) {
        match f {
            SmtFormula::Fun(fun, args) if fun == &eval.m /* || fun == &eval.c */ => {
                *f = args[0].clone();
                aux(f, eval)
            }
            SmtFormula::Forall(_, arg) | SmtFormula::Exists(_, arg) => aux(&mut *arg, eval),
            SmtFormula::Fun(_, args)
            | SmtFormula::Neq(args)
            | SmtFormula::Eq(args)
            | SmtFormula::And(args)
            | SmtFormula::Or(args) => args.iter_mut().for_each(|arg| aux(arg, eval)),
            SmtFormula::Ite(c, r, l) => [c, l, r].into_iter().for_each(|arg| aux(arg, eval)),
            _ => {}
        }
    }

    for a in assertions.iter_mut() {
        match a {
            Smt::Assert(f) | Smt::AssertNot(f) => aux(f, &eval),
            _ => {}
        }
    }
}

pub fn problem_smts_with_lemma(pbl: Problem) -> impl Iterator<Item = Vec<Smt>> {
    let Problem {
        steps,
        memory_cells,
        env,
        mut assertions,
        query,
        order,
        lemmas,
        crypto_assumptions,
        quantifiers,
    } = pbl;

    // the last lemma is the query
    // lemmas.push(query);

    // let mut verified_lemmas: Vec<RichFormula> = Vec::new();

    lemmas
        .into_iter()
        .chain(std::iter::once(query))
        .map(move |lemma| {
            // this hurts a little ^^'
            let pbl = Problem {
                steps: steps.clone(),
                memory_cells: memory_cells.clone(),
                env: env.clone(),
                assertions: assertions.clone(),
                query: lemma.clone(),
                order: order.clone(),
                lemmas: vec![],
                crypto_assumptions: crypto_assumptions.clone(),
                quantifiers: quantifiers.clone(),
            };

            let smt = problem_to_smt(pbl);
            // let end = smt.iter().skip_while(|&s| s != &Smt::CheckSat).cloned().collect_vec();
            // smt.extend(
            //     verified_lemmas
            //         .iter()
            //         .map(|old_lemma| Smt::Assert(old_lemma.clone().into())),
            // );

            // verified_lemmas.push(lemma);
            assertions.push(lemma);

            smt
        })
}
