use cryptovampire_smt::SmtSink;
use egg::{Analysis, EGraph};

use crate::libraries::utils::{EggRewriteSink, RewriteSink, RuleSink};
use crate::problem::PAnalysis;
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
    fn add_static_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {}

    fn add_dynamic_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {}

    fn add_all_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {
        Self::add_static_smt(pbl, sink);
        Self::add_dynamic_smt(pbl, sink);
    }

    /// cryptovampire rewrites
    fn add_static_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {}

    /// cryptovampire rewrites
    fn add_dynamic_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {}

    fn add_all_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {
        Self::add_static_rewrites(pbl, sink);
        Self::add_dynamic_rewrites(pbl, sink);
    }

    /// egg rewrites
    fn add_static_egg_rewrites<N: Analysis<Lang>>(
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
    }

    /// egg_rewrite
    fn add_dynamic_egg_rewrites<N: Analysis<Lang>>(
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
    }

    fn add_all_egg_rewrites<N: Analysis<Lang>>(
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        Self::add_static_egg_rewrites(pbl, sink);
        Self::add_dynamic_egg_rewrites(pbl, sink);
    }

    /// golgge rule
    fn add_static_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {}

    /// golgge rule
    fn add_dynamic_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {}

    fn add_all_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {
        Self::add_static_rules(pbl, sink);
        Self::add_dynamic_rules(pbl, sink);
    }

    /// initialize the egraph. This where a library can put initial elements
    /// into the running egraph. (access to [`Problem`] is done thourgh `egraph`
    /// [Analysis])
    fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {}
}
