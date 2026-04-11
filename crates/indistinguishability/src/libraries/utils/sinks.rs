use std::any::Any;
use std::fmt::Display;

use bitflags::bitflags;
use egg::Analysis;
use golgge::Rule;
use utils::reservable::Reservable;
use utils::{ereturn_let, implvec};

use crate::problem::{PAnalysis, RcRule};
use crate::terms::Rewrite;
use crate::{Lang, MSmt, MSmtFormula, Problem};

/// Specialized sink trait for prolog rules ([RcRule]).
#[allow(deprecated)]
pub trait RuleSink {
    /// internal use only. Prefer `extend_rules`
    #[deprecated]
    fn extend_rc_rules(&mut self, iter: implvec!(RcRule));

    /// reserve space
    fn reserve(&mut self, size: usize);

    /// internal use only. Prefer `add_rule`
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

    /// use `add_rule` instead
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

    /// reserve space
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

    /// reserve space
    fn reserve(&mut self, size: usize) {
        Reservable::gen_reserve(self, size);
    }
}

/// Specialized sink trait for internal rewrites ([Rewrite]).
pub trait RewriteSink {
    fn extend_rewrites(&mut self, pbl: &Problem, iter: implvec!(Rewrite));
    fn reserve(&mut self, size: usize);

    fn add_rewrite(&mut self, pbl: &Problem, rewrite: Rewrite) {
        self.extend_rewrites(pbl, [rewrite]);
    }
}

impl<V> RewriteSink for V
where
    V: Extend<Rewrite> + Reservable,
{
    fn extend_rewrites(&mut self, _: &Problem, iter: implvec!(Rewrite)) {
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        Reservable::gen_reserve(self, size);
    }
}

pub trait SmtSink<'a> {
    fn extend_smt(&mut self, pbl: &Problem, options: &SmtOption, iter: implvec!(MSmt<'a>));
    fn reserve(&mut self, size: usize);

    fn extend_one_smt(&mut self, pbl: &Problem, options: &SmtOption, smt: MSmt<'a>) {
        self.extend_smt(pbl, options, Some(smt));
    }

    fn assert_many(&mut self, pbl: &Problem, options: &SmtOption, iter: implvec!(MSmtFormula<'a>)) {
        self.extend_smt(pbl, options, iter.into_iter().map(MSmt::mk_assert));
    }

    fn assert_one(&mut self, pbl: &Problem, options: &SmtOption, formula: MSmtFormula<'a>) {
        self.assert_many(pbl, options, Some(formula));
    }

    fn comment(&mut self, pbl: &Problem, options: &SmtOption, comment: impl Display) {
        self.extend_one_smt(pbl, options, MSmt::Comment(comment.to_string()));
    }

    fn comment_block(&mut self, pbl: &Problem, options: &SmtOption, comment: impl Display) {
        self.extend_one_smt(pbl, options, MSmt::comment_block(comment.to_string()));
    }
}

#[derive(Debug, Clone, Copy)]
pub struct SmtOption {
    pub depend_on_context: bool,
}

pub static INDEPEDANT_QUERY: SmtOption = SmtOption {
    depend_on_context: false,
};

impl Default for SmtOption {
    fn default() -> Self {
        Self {
            depend_on_context: true,
        }
    }
}

impl<'a, V> SmtSink<'a> for V
where
    V: Extend<MSmt<'a>> + Reservable,
{
    fn extend_smt(&mut self, _: &Problem, _: &SmtOption, iter: implvec!(MSmt<'a>)) {
        let iter = iter
            .into_iter()
            .inspect(|f| debug_assert!(no_garabage(f), "garbage in {f}"));
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        self.gen_reserve(size);
    }
}

fn no_garabage<'a>(smt: &MSmt<'a>) -> bool {
    match smt {
        cryptovampire_smt::Smt::Assert(formula)
        | cryptovampire_smt::Smt::AssertTh(formula)
        | cryptovampire_smt::Smt::AssertNot(formula) => no_garabagef(formula),
        _ => true,
    }
}

fn no_garabagef<'a>(f: &MSmtFormula<'a>) -> bool {
    match f {
        MSmtFormula::Fun(fun, args) => {
            !fun.is_garabage_collectable() && args.iter().all(|f| no_garabagef(f))
        }
        MSmtFormula::Exists(_, arg) | MSmtFormula::Forall(_, arg) => no_garabagef(arg),
        _ => true,
    }
}
