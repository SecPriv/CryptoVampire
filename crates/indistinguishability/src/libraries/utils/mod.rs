use egg::{Analysis, EGraph, Id, Language};
use itertools::Itertools;
use rustc_hash::FxHashSet;
/// Re-exports `EgraphSearcher` for e-graph based searching, `SyntaxSearcher` for syntax-based searching,
/// and `default_is_special` for determining if a function is special.
pub use subterm_trait::{EgraphSearcher, SyntaxSearcher, default_is_special};
use utils::{econtinue_if, implvec};

use crate::{
    Lang,
    problem::PAnalysis,
    protocol::Protocol,
    terms::{Function, IS_INDEX, Sort},
};
/// Provides utilities for handling fresh variables and formulas.
pub mod fresh;

mod subterm_trait;

pub(crate) mod lambda_subst;

mod side;
pub use side::Side;

mod with_data;
pub use with_data::{RuleWithFreshNonce, FreshNonceSet};

// mod subst;
// pub use subst::mk_subst_rw;

// pub fn generate_rule_vars_arr<const N: usize>(
//     fun: &Function,
// ) -> (Vec<[LangVar; 1]>, [[LangVar; 1]; N]) {
//     use egg::*;
//     let (vars, others) = generate_rule_vars0(fun);
//     let vars: Vec<[LangVar; 1]> = vars.map(ENodeOrVar::Var).map(|x| [x]).collect();
//     let others = others.map(ENodeOrVar::Var).map(|x| [x]);
//     (vars, others)
// }

// pub fn generate_rule_vars<const N: usize>(fun: &Function) -> (Vec<LangVar>, [LangVar; N]) {
//     use egg::*;
//     let (vars1, others1) = generate_rule_vars0(fun);

//     let vars: Vec<LangVar> = vars1.map(ENodeOrVar::Var).collect();
//     let others = others1.map(ENodeOrVar::Var);
//     (vars, others)
// }

// pub fn generate_rule_vars0<const N: usize>(
//     fun: &Function,
// ) -> (impl Iterator<Item = Var> + Clone + use<'_, N>, [Var; N]) {
//     use egg::*;
//     let n = fun.signature.inputs.len() as u32;
//     let vars1 = fun
//         .signature
//         .inputs
//         .iter()
//         .enumerate()
//         .map(|(i, _)| Var::from_usize(i as u32));
//     let others1 = ::std::array::from_fn(|i| i as u32)
//         .map(|x| x + n)
//         .map(Var::from_usize);
//     (vars1, others1)
// }

pub fn find_available_id<'e>(
    egraph: &mut EGraph<Lang, PAnalysis<'e>>,
    sort: Sort,
    ids_to_check: implvec!(Id),
) -> Id {
    // *all* the subterms of `ids_to_check`
    let used_ids = all_descendants(egraph, ids_to_check, can_have_childrens);
    // the usable cached ids
    let relevant_generated_ids: FxHashSet<_> = egraph
        .analysis
        .pbl()
        .state
        .generated_ids
        .iter()
        .filter(|x| {
            egraph[**x]
                .nodes
                .iter()
                .any(|l| l.head.signature.output == sort)
        })
        .copied()
        .collect();
    if let Some(id) = relevant_generated_ids.difference(&used_ids).next().copied() {
        return id;
    }

    let new_var = egraph
        .analysis
        .pbl_mut()
        .declare_function()
        .output(sort)
        .fresh_name("idx")
        .call();
    let new_var = egraph.add(Lang::new(new_var, []));
    egraph.add(IS_INDEX.app_id([new_var]));
    egraph
        .analysis
        .pbl_mut()
        .state
        .generated_ids
        .insert(new_var);
    new_var
}

pub fn all_descendants<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    ancestors: implvec!(Id),
    mut can_have_childrens: impl FnMut(&Function) -> bool,
) -> FxHashSet<Id> {
    let mut todo = ancestors.into_iter().collect_vec();
    let mut descendants = FxHashSet::default();
    while let Some(x) = todo.pop() {
        econtinue_if!(descendants.contains(&x));
        descendants.insert(x);
        todo.extend(
            egraph[x]
                .nodes
                .iter()
                .filter(|f| can_have_childrens(&f.head))
                .flat_map(|f| f.children())
                .cloned(),
        );
    }
    descendants
}

fn can_have_childrens(f: &Function) -> bool {
    !f.is_alias()
}

pub fn get_protocol<'a, 'b>(
    egraph: &'b egg::EGraph<Lang, PAnalysis<'a>>,
    id: Id,
) -> Option<&'b Protocol> {
    // let id = subst.get(P.as_egg()).unwrap();
    let idx = egraph[id]
        .iter()
        .find_map(|f| f.head.get_protocol_index())?;
    // there has to be one
    egraph.analysis.pbl().protocols().get(idx)
}
