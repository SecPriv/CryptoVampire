// QUESTION: Should we cross reference existential quantifiers?
use std::ops::Deref;

use egg::{ENodeOrVar, Pattern, Var};
use golgge::PrologRule;
use itertools::{Itertools, chain};

use crate::rules::deduce::{self, GetDeduce};
use crate::terms::utils::offset;
use crate::terms::{Quantifier, QuantifierT};
use crate::{Lang, Problem};

pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    debug_assert!(pbl.function.valid());
    pbl.function.quantifiers().iter().map(|q| match q {
        Quantifier::Exists(q) => mk_quantifier_deduce_rules_one(pbl, q),
        Quantifier::FindSuchThat(q) => mk_quantifier_deduce_rules_one(pbl, q),
    })
}

/// Generate the rule for a single quantifier
/// Funilly enough it's the same thing for exists and fdst
fn mk_quantifier_deduce_rules_one<Q: QuantifierT>(_pbl: &Problem, e: &Q) -> PrologRule<Lang> {
    let deduce = e.top_level_function().get_deduce();
    let max_var: u32 = chain![e.cvars(), e.bvars()]
        .flat_map(|v| v.as_u32())
        .max()
        .unwrap_or(0)
        + 1;

    // initiate the variables
    let [u, v, h1, h2] = ::std::array::from_fn(|i| [ENodeOrVar::Var(Var::from_u32(i as u32))]);
    let base_vars_n = 4;

    // u, v |> exits(vecx, vecsk(vecx)), exists(vecy, vecsk(vecy)) # h1, h2
    let input = {
        let mk_applied = |start: u32| {
            let cvars = e
                .cvars()
                .iter()
                .map(|&v| offset::var(start, v))
                .map(|v| vec![ENodeOrVar::Var(v)].into())
                .collect_vec();
            let bvars = e.skolems().iter().map(|f| f.app_var(&cvars)).collect_vec();
            let args = chain![cvars, bvars].collect_vec();
            e.top_level_function().app_var(&args)
        };

        let left = mk_applied(base_vars_n);
        let right = mk_applied(base_vars_n + max_var);
        deduce.app_var(
            &chain![
                [u.as_slice(), v.as_slice()],
                [left.deref(), right.deref()],
                [h1.as_slice(), h2.as_slice()]
            ]
            .collect_vec(),
        )
    };

    // u, v |> exits(vecx, vecfresh), exists(vecy, vecfresh) # h1, h2
    let dep = {
        let mk_fresh = |start: u32| {
            let cvars = e
                .cvars()
                .iter()
                .map(|&v| offset::var(start, v))
                .map(|v| vec![ENodeOrVar::Var(v)].into())
                .collect_vec();
            let bvars = e
                .fresh_indices()
                .iter()
                .map(|f| f.app_empty_var())
                .collect_vec();
            let args = chain![cvars, bvars].collect_vec();
            e.top_level_function().app_var(&args)
        };

        let left = mk_fresh(base_vars_n);
        let right = mk_fresh(base_vars_n + max_var);
        deduce.app_var(
            &chain![
                [u.as_slice(), v.as_slice()],
                [left.deref(), right.deref()],
                [h1.as_slice(), h2.as_slice()]
            ]
            .collect_vec(),
        )
    };

    PrologRule {
        input: Pattern::from(input),
        deps: vec![Pattern::from(dep)],
        cut: false,
        require_decrease: false,
        name: Some(format!("deduce {}", e.top_level_function().name)),
    }
}
