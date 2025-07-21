use egg::{ENodeOrVar, Id};
use itertools::{Itertools, chain};
use logic_formula::egg::SimpleDiscriminant;

use crate::rules::PRF;
use crate::rules::utils::generate_rule_vars0;
use crate::terms::{Function, NONCE, Rewrite, Sort};
use crate::{Problem, rexp};

pub fn mk_rewrites<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = Rewrite> + use<'a> {
    chain![[mk_rewrite_init(pbl, prf)], mk_rewrite_regular(pbl, prf)]
}

/// for `f != hash` this builds for all `n`
/// ```text
/// h(m, nonce(k))
///     -> candidate(h(m, nonce(k)), m, k)
/// ```
fn mk_rewrite_init<'a>(
    _pbl: &'a Problem,
    PRF {
        hash,
        candidate_bitstring: candidate,
        ..
    }: &'a PRF,
) -> Rewrite {
    Rewrite::builder()
        .prolog_only(true)
        .from(rexp!((hash #1 (NONCE #2))))
        .to(rexp!((candidate (hash #1 (NONCE #2)) #1 #2)))
        .variables([1, 2].map(egg::Var::from_u32))
        .sorts([Sort::Bitstring, Sort::Nonce])
        .name(format!("candidate prf success ({hash})"))
        .build()
}

fn mk_rewrite_regular<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = Rewrite> {
    pbl.function
        .iter()
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| (!f.is_special_subterm()) || f.is_if_then_else())
        .flat_map(|f| mk_rewrite_one(pbl, prf, f))
}

/// for `f != hash` this builds for all `n`
/// ```text
/// f(x1,..., xn, candidate(x(n+1), m, k), ...,xm)
///     -> candidate(f(x1,...,xm), m, k)
/// ```
fn mk_rewrite_one<'a>(
    _pbl: &'a Problem,
    prf: &'a PRF,
    f: &'a Function,
) -> impl Iterator<Item = Rewrite> + use<'a> {
    let (vars0, extra_vars0) = generate_rule_vars0(f);

    // variables for the arguments
    let vars = vars0.clone().map(ENodeOrVar::Var);
    // m, k
    let extra_vars @ [_, _] = extra_vars0.map(ENodeOrVar::Var);

    let all_vars = chain![vars0, extra_vars0];
    let sorts = chain![
        f.signature.inputs.iter().cloned(),
        [Sort::Bitstring, Sort::Nonce]
    ];
    let n = f.arity();

    let candidate = prf.get_candidate(f.signature.output).unwrap();

    f.signature
        .inputs
        .iter()
        .enumerate()
        .filter_map(|(i, s)| prf.get_candidate(*s).map(|f| (i, f)))
        .map({
            move |(i, candidate_x)| {
                let premise = chain![
                    vars.clone(),
                    extra_vars.clone(),
                    [
                        candidate_x.app_id([i, n, n + 1].map(Id::from)),
                        f.app_id(chain![0..i, [n + 2], (i + 1)..n].map_into())
                    ]
                    .map(ENodeOrVar::ENode)
                ];
                let conclusion = chain![
                    vars.clone(),
                    extra_vars.clone(),
                    [
                        f.app_id(chain![0..n].map_into()),
                        candidate.app_id([n + 2, n, n + 1].map(Id::from)),
                    ]
                    .map(ENodeOrVar::ENode)
                ];

                Rewrite::builder()
                    .prolog_only(true)
                    .variables(all_vars.clone())
                    .sorts(sorts.clone())
                    .from(premise)
                    .to(conclusion)
                    .name(format!("candidate prf {f} arg#{i:}"))
                    .build()
            }
        })
}
