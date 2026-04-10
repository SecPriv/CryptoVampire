use egg::{Analysis, EGraph};

use crate::libraries::utils::{EggRewriteSink, RewriteSink, RuleSink, SmtSink};
use crate::problem::PAnalysis;
use crate::problem::cache::Context;
use crate::{Lang, MSmtParam, Problem};

/// A library that need to initialize axioms and rules
///
/// NB: the split static/dynamic isn't really taken into account currently. The
/// idea is that rules should go into static only if they do not need to be
/// recomputed during a run. But it is a bit unclear at the moment under which
/// conditions this could be ever true...
#[allow(unused)]
pub trait Library {
    /// Add smt axioms that do not change during a run
    fn add_smt<'a>(&self, pbl: &mut Problem, context: &Context, sink: &mut impl SmtSink<'a>) {}

    /// cryptovampire rewrites
    fn add_rewrites(&self, pbl: &mut Problem, sink: &mut impl RewriteSink) {}

    /// egg rewrites
    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
    }

    /// golgge rule
    fn add_rules(&self, pbl: &mut Problem, sink: &mut impl RuleSink) {}

    /// initialize the egraph. This where a library can put initial elements
    /// into the running egraph. (access to [`Problem`] is done thourgh `egraph`
    /// [Analysis])
    fn modify_egraph<'a>(&self, egraph: &mut EGraph<Lang, PAnalysis<'a>>) {}
}
