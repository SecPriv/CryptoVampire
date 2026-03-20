use cryptovampire_smt::SmtSink;
use egg::{Analysis, EGraph};

use crate::libraries::utils::{EggRewriteSink, RewriteSink, RuleSink};
use crate::problem::PAnalysis;
use crate::{Lang, MSmtParam, Problem};

#[allow(unused)]
pub trait Library {
    fn add_static_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {}

    fn add_dynamic_smt(pbl: &mut Problem, sink: &mut impl SmtSink<MSmtParam>) {}

    /// rewrites that don't depend on the current step
    fn add_static_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {}

    /// rewrites that depend on the current step
    fn add_dynamic_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {}

    /// rewrites that don't depend on the current step
    fn add_static_egg_rewrites<N:Analysis<Lang>>(pbl: &mut Problem, sink: &mut impl EggRewriteSink<N>) {}

    /// rewrites that depend on the current step
    fn add_dynamic_egg_rewrites<N:Analysis<Lang>>(pbl: &mut Problem, sink: &mut impl EggRewriteSink<N>) {}

    fn add_static_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {}

    fn add_dynamic_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {}
    fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {}
}