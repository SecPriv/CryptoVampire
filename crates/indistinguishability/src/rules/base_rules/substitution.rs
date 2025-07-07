//! definition of the `subst` rewrite rules
//!
//! ```text
//! subst(m, x, y) -> m[x -> y]
//! ```

use egg::{Analysis, ENodeOrVar, Pattern, PatternAst, Rewrite};
use itertools::{Itertools, chain};
use logic_formula::egg::SimpleDiscriminant;

use crate::{
    Lang, Problem, rexp,
    terms::{Function, SUBSTITUTION},
};

fn mk_rw_one<N: Analysis<Lang>>(pbl: &Problem, f: &Function) -> Rewrite<Lang, N> {
    let vars = f
        .signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, _)| egg::Var::from_u32(i as u32))
        .map(ENodeOrVar::Var)
        .collect_vec();
    let n = vars.len();
    let [x, y] = [1, 2]
        .map(|x| x + n as u32)
        .map(egg::Var::from_u32)
        .map(ENodeOrVar::Var);

    let premise: PatternAst<Lang> = chain![
        vars.iter().cloned(),
        [x.clone(), y.clone()],
        [
            f.app_id((0..n).map_into()),
            SUBSTITUTION.app_id([n + 2, n, n + 1].into_iter().map_into())
        ]
        .map(ENodeOrVar::ENode)
    ]
    .collect();
    let conclusion: PatternAst<_> = chain![
        vars,
        [x, y],
        (0..n)
            .map(|i| SUBSTITUTION.app_id([i, n, n + 1].into_iter().map_into()))
            .map(ENodeOrVar::ENode),
        [f.app_id((0..n).map(|i| n + 2 + i).map_into())].map(ENodeOrVar::ENode)
    ]
    .collect();

    Rewrite::new(
        format!("subst_{f}"),
        Pattern::from(premise),
        Pattern::from(conclusion),
    )
    .unwrap()
}

fn mk_rw_base<N: Analysis<Lang>>() -> Rewrite<Lang, N> {
    let premise: PatternAst<Lang> = rexp!((SUBSTITUTION #1 #1 #2)).into_iter().collect();
    let conclusion: PatternAst<Lang> = rexp!(#2).into_iter().collect();

    Rewrite::new(
        "subst_base",
        Pattern::from(premise),
        Pattern::from(conclusion),
    )
    .unwrap()
}
