use std::borrow::Cow;

use egg::{Analysis, EGraph, Pattern, SearchMatches, Searcher};
use static_init::dynamic;

use crate::problem::{CurrentStep, PAnalysis};
use crate::terms::{Formula, IS_INDEX, Sort};
use crate::{Lang, rexp};

pub fn mk_rewrite<N: Analysis<Lang>>() -> egg::Rewrite<Lang, N> {
    mk_rewrite!("eq_indices"; (i): (IS_INDEX #i) => (#i))
}
pub fn modify_egraph<'pbl>(egraph: &mut EGraph<Lang, PAnalysis<'pbl>>) {
    let CurrentStep { args, .. } = egraph.analysis.pbl().current_step().unwrap().clone();
    for arg in args {
        egraph.add_expr(&rexp!((IS_INDEX arg)).as_egg_ground());
    }
}
