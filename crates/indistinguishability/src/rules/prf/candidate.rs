use egg::{Analysis, ENodeOrVar, Id, Pattern, PatternAst, Rewrite};
use itertools::{Itertools, chain};
use logic_formula::egg::SimpleDiscriminant;
use steel::rvals::CustomType;

use crate::{
    Lang, Problem, rexp,
    rules::{
        PRF,
        prf::candidate,
        utils::{generate_rule_vars, generate_rule_vars_arr},
    },
    terms::{Function, NONCE, Sort},
};

pub fn mk_rewrites<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
    prf: &'a PRF,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    chain![[mk_rewrite_init(pbl, prf)], mk_rewrite_regular(pbl, prf)]
}

/// for `f != hash` this builds for all `n`
///```text
/// h(m, nonce(k))
///     -> candidate(h(m, nonce(k)), m, k)
/// ```
fn mk_rewrite_init<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
    PRF {
        hash,
        candidate_bitstring: candidate,
        ..
    }: &'a PRF,
) -> Rewrite<Lang, N> {
    let premise = rexp!((hash #1 (NONCE #2)));
    let conclusion = rexp!((candidate (hash #1 (NONCE #2)) #1 #2));
    Rewrite::new(
        format!("{candidate}_m_init"),
        Pattern::new(premise.into_iter().collect()),
        Pattern::new(conclusion.into_iter().collect()),
    )
    .unwrap()
}

fn mk_rewrite_regular<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
    prf: &'a PRF,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    pbl.function
        .iter()
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm() || f.is_if_then_else())
        .flat_map(|f| mk_rewrite_one(pbl, prf, f))
}

/// for `f != hash` this builds for all `n`
///```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
fn mk_rewrite_one<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
    prf: &'a PRF,
    f: &'a Function,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    let (vars, [m, k]) = generate_rule_vars(&f);
    let n = vars.len();

    let candidate = prf.get_candidate(f.signature.output).unwrap();

    f.signature
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(i, s)| prf.get_candidate(*s).map(|f| (i, f)))
        .map({
            move |(i, candidate_x)| {
                let premise: PatternAst<Lang> = chain![
                    vars.iter().cloned(),
                    [m.clone(), k.clone()],
                    [
                        candidate_x.app_id([i, n + 1, n + 2].map(Id::from)),
                        f.app_id(chain![0..i, [n + 3], (i + 1)..n].map_into())
                    ]
                    .map(ENodeOrVar::ENode)
                ]
                .collect();
                let conclusion: PatternAst<Lang> = chain![
                    vars.iter().cloned(),
                    [m.clone(), k.clone()],
                    [
                        f.app_id(chain![0..n].map_into()),
                        candidate.app_id([n + 3, n + 1, n + 2].map(Id::from)),
                    ]
                    .map(ENodeOrVar::ENode)
                ]
                .collect();

                Rewrite::new(
                    format!("{}_{}", candidate.name(), f.name()),
                    Pattern::from(premise),
                    Pattern::from(conclusion),
                )
                .unwrap()
            }
        })
}
