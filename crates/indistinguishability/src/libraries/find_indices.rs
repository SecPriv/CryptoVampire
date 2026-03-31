use std::borrow::Cow;

use egg::{Analysis, EGraph, Pattern, SearchMatches, Searcher};
use static_init::dynamic;

use crate::libraries::Library;
use crate::problem::{CurrentStep, PAnalysis};
use crate::terms::{Formula, IS_INDEX, Sort};
use crate::{Lang, rexp};

pub struct FindIndicesLib;

impl Library for FindIndicesLib {
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        _pbl: &mut crate::Problem,
        sink: &mut impl super::utils::EggRewriteSink<N>,
    ) {
        sink.add_egg_rewrite(mk_rewrite!("eq_indices"; (i): (IS_INDEX #i) => (#i)));
    }

    fn modify_egraph<'a>(&self, egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
        let CurrentStep { args, .. } = egraph.analysis.pbl().current_step().unwrap().clone();
        for arg in args {
            egraph.add_expr(&rexp!((IS_INDEX arg)).as_egg_ground());
        }
    }
}
