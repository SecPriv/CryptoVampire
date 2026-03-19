use std::any::Any;

use egg::Analysis;
use golgge::Rule;
use utils::implvec;
use utils::reservable::Reservable;

use crate::Lang;
use crate::problem::{PAnalysis, RcRule};
use crate::terms::Rewrite;

/// Specialized sink trait for prolog rules ([RcRule]).
pub trait RuleSink {
    #[deprecated]
    fn extend_rc_rules(&mut self, iter: implvec!(RcRule));

    fn reserve(&mut self, size: usize);

    #[deprecated]
    fn add_rc_rule(&mut self, rule: RcRule) {
        self.extend_rc_rules(Some(rule));
    }

    fn extend_rules<R>(&mut self, iter: implvec!(R))
    where
        R: for<'a> Rule<Lang, PAnalysis<'a>, RcRule>,
        R: Sized + Any + Sync + Send + 'static,
    {
        use crate::problem::PRule;
        self.extend_rc_rules(iter.into_iter().map(PRule::into_mrc));
    }

    fn add_rule<R>(&mut self, rule: R)
    where
        R: for<'a> Rule<Lang, PAnalysis<'a>, RcRule>,
        R: Sized + Any + Sync + Send + 'static,
    {
        use crate::problem::PRule;
        self.add_rc_rule(rule.into_mrc());
    }

    #[deprecated]
    fn add_prolog_rule(&mut self, rule: golgge::PrologRule<crate::Lang>) {
        use crate::problem::PRule;
        self.add_rc_rule(rule.into_mrc());
    }
}

impl<V> RuleSink for V
where
    V: Extend<RcRule> + Reservable,
{
    fn extend_rc_rules(&mut self, iter: implvec!(RcRule)) {
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        Reservable::gen_reserve(self, size);
    }
}

/// Specialized sink trait for egg rewrites ([egg::Rewrite]).
pub trait EggRewriteSink<N: Analysis<Lang>> {
    fn extend_egg_rewrites(&mut self, iter: implvec!(egg::Rewrite<Lang, N>));
    fn reserve(&mut self, size: usize);

    fn add_egg_rewrite(&mut self, rewrite: egg::Rewrite<Lang, N>) {
        self.extend_egg_rewrites([rewrite]);
    }
}

impl<N, V> EggRewriteSink<N> for V
where
    N: Analysis<Lang>,
    V: Extend<egg::Rewrite<Lang, N>> + Reservable,
{
    fn extend_egg_rewrites(&mut self, iter: implvec!(egg::Rewrite<Lang, N>)) {
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        Reservable::gen_reserve(self, size);
    }
}

/// Specialized sink trait for internal rewrites ([Rewrite]).
pub trait RewriteSink {
    fn extend_rewrites(&mut self, iter: implvec!(Rewrite));
    fn reserve(&mut self, size: usize);

    fn add_rewrite(&mut self, rewrite: Rewrite) {
        self.extend_rewrites([rewrite]);
    }
}

impl<V> RewriteSink for V
where
    V: Extend<Rewrite> + Reservable,
{
    fn extend_rewrites(&mut self, iter: implvec!(Rewrite)) {
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        Reservable::gen_reserve(self, size);
    }
}
