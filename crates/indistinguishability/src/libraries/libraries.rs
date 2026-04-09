use std::marker::PhantomData;
use std::sync::atomic::{AtomicUsize, Ordering};

use egg::{Analysis, EGraph, Pattern, PatternAst};
use log::{debug, log_enabled, trace};
use utils::econtinue_if;

use super::Library;
use crate::libraries::and_bounder::AndBounderLib;
use crate::libraries::base::BaseRewriteLib;
use crate::libraries::constrains::ConstrainsLib;
use crate::libraries::current_step::CurrentStep;
use crate::libraries::deduce::DeduceLib;
use crate::libraries::fa::FaLib;
use crate::libraries::find_indices::FindIndicesLib;
use crate::libraries::ifs::IfLib;
use crate::libraries::lambda::LambdaLib;
use crate::libraries::memory_cells::MemoryCellLib;
use crate::libraries::nonce::NonceLib;
use crate::libraries::problem::ProblemLib;
use crate::libraries::protocol::unfold::UnfoldLib;
use crate::libraries::publication::PublicationLib;
use crate::libraries::sanity_check::SanityCheck;
use crate::libraries::smt::SmtLib;
use crate::libraries::substitution::SubstLib;
use crate::libraries::utils::{EggRewriteSink, INDEPEDANT_QUERY, RewriteSink, RuleSink, SmtSink};
use crate::libraries::vampire::VampireLib;
use crate::problem::cache::Context;
use crate::problem::{PAnalysis, ProblemState, ProblemStateLib, RcRule};
use crate::{CVProgram, Lang, LangVar, MSmtParam, Problem, smt};

macro_rules! mk_libraires {
  ($name:ty; $($libs:ident),* $(,)*) => {
        impl Library for $name {
            fn add_smt<'a>(&self, pbl: &mut Problem, context: &Context, sink: &mut impl SmtSink<'a>) {
                $($libs.add_smt(pbl, context, sink));*
            }

            fn add_rewrites(&self, pbl: &mut Problem, sink: &mut impl RewriteSink) {
                $($libs.add_rewrites(pbl, sink));*
            }

            fn add_egg_rewrites<N:Analysis<Lang>>(&self, pbl: &mut Problem, sink: &mut impl EggRewriteSink<N>) {
                $($libs.add_egg_rewrites(pbl, sink));*
            }

            fn add_rules(&self, pbl: &mut Problem, sink: &mut impl RuleSink) {
                $($libs.add_rules(pbl, sink));*
            }

            fn modify_egraph<'a>(&self, egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
                $($libs.modify_egraph(egraph));*
            }
        }
  };
}

struct Wrapper<'a, U, V>(&'a mut U, V);

static EGG_REWRITE_COUNTER: AtomicUsize = AtomicUsize::new(0);

impl<'a, N: Analysis<Lang>, U: EggRewriteSink<N>> RewriteSink for Wrapper<'a, U, PhantomData<N>> {
    fn extend_rewrites(&mut self, _: &Problem, iter: utils::implvec!(crate::terms::Rewrite)) {
        let iter = iter
            .into_iter()
            .map(|crate::terms::Rewrite { from, to, name, .. }| {
                let name = name
                    .as_ref()
                    .cloned()
                    .unwrap_or_else(|| {
                        format!(
                            "extra rewrite #{}",
                            EGG_REWRITE_COUNTER.fetch_add(1, Ordering::AcqRel)
                        )
                        .into()
                    })
                    .into_owned();
                trace!("registering rw rule {name} to egg...");

                let from = from.as_egg_non_capture_avoiding::<LangVar>();
                egg::Rewrite::new(
                    name,
                    Pattern::from(PatternAst::from(from)),
                    Pattern::from(&to),
                )
                .unwrap()
            });

        self.0.extend_egg_rewrites(iter);
    }

    fn reserve(&mut self, size: usize) {
        self.0.reserve(size);
    }
}

impl<'a, 'b, U: SmtSink<'b>> RewriteSink for Wrapper<'a, U, ()> {
    fn extend_rewrites(&mut self, pbl: &Problem, iter: utils::implvec!(crate::terms::Rewrite)) {
        let iter = iter.into_iter();
        let (size_hint, _) = iter.size_hint();
        self.0.reserve(2 * size_hint);
        for crate::terms::Rewrite {
            from,
            to,
            variables,
            prolog_only,
            name,
            ..
        } in iter
        {
            econtinue_if!(prolog_only);

            if let Some(name) = name {
                self.0.comment(pbl, &Default::default(), name);
            }
            let vars = variables.clone().into_owned();

            let from = from.as_smt(pbl).unwrap();

            match to.try_evaluate() {
                Some(true) => {
                    self.0
                        .assert_one(pbl, &Default::default(), smt!((forall #vars #from)))
                }
                Some(false) => {
                    self.0
                        .assert_one(pbl, &Default::default(), smt!((forall #vars (not #from))))
                }
                None => {
                    let to = to.as_smt(pbl).unwrap();
                    self.0
                        .assert_one(pbl, &Default::default(), smt!((forall #vars (= #from #to))))
                }
            }
        }
    }

    fn reserve(&mut self, size: usize) {
        self.0.reserve(2 * size);
    }
}

pub struct Libraries;

impl Libraries {
    pub fn add_all_smt<'a>(pbl: &mut Problem, context: &Context, sink: &mut impl SmtSink<'a>) {
        Self.add_smt(pbl, context, sink);

        sink.comment_block(pbl, &INDEPEDANT_QUERY, "Cross engine rewrites");
        sink.comment(
            pbl,
            &INDEPEDANT_QUERY,
            "this include custom rewrites and library rewrites",
        );

        Self::add_all_rewrites(pbl, &mut Wrapper(sink, ()));
    }

    pub fn add_all_rewrites(pbl: &mut Problem, sink: &mut impl RewriteSink) {
        Self.add_rewrites(pbl, sink);
    }

    pub fn add_all_egg_rewrites<N: Analysis<Lang>>(
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        Self.add_egg_rewrites(pbl, sink);

        Self::add_all_rewrites(pbl, &mut Wrapper(sink, Default::default()));
    }

    pub fn add_all_rules(pbl: &mut Problem, sink: &mut impl RuleSink) {
        Self.add_rules(pbl, sink);
    }

    /// Add terms to the egraph / union terms
    pub fn init_egraph<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
        Self.modify_egraph(egraph);

        if cfg!(debug_assertions) && log_enabled!(log::Level::Debug) {
            debug_init_egraph(egraph);
        }
    }

    /// Creates the default prolog rules
    ///
    /// This function creates the default prolog rules for the given problem.
    /// It includes the extra rules from the problem, the deduce rules, the forall rules,
    /// and the substitution rule.
    /// In debug mode, it also includes the sanity check rule.
    pub fn mk_all_rules(pbl: &mut Problem) -> Vec<RcRule> {
        let mut sink = Vec::new();
        Self::add_all_rules(pbl, &mut sink);
        sink
    }

    /// Creates the default rewrite rules
    ///
    /// This function creates the default rewrite rules for the given problem.
    /// It includes the default rewrites and the lambda rewrites.
    pub fn mk_all_egg_rewrites<'a>(pbl: &mut Problem) -> Vec<egg::Rewrite<Lang, PAnalysis<'a>>> {
        let mut sink = Vec::new();
        Self::add_all_egg_rewrites(pbl, &mut sink);
        sink
    }

    pub fn recompute_egg_rewrite_rules<'a>(prgm: &mut CVProgram<'a>) {
        let mut eq_rules = prgm.take_eq_rules();

        Self::add_all_egg_rewrites(prgm.egraph_mut().analysis.pbl_mut(), &mut eq_rules);

        prgm.set_eq_rules(eq_rules);
    }
}

#[inline(never)]
fn debug_init_egraph<N: Analysis<Lang>>(egraph: &mut EGraph<Lang, N>) {
    let tmp = tempfile::Builder::new()
        .suffix(".pdf")
        .prefix("egraph-")
        .disable_cleanup(true)
        .tempfile()
        .unwrap();
    egraph.dot().to_pdf(&tmp).unwrap();
    debug!("rendered init egraph in {tmp:?}");
}

mk_libraires!(Libraries;
  AndBounderLib,
  SmtLib,
  BaseRewriteLib,
  UnfoldLib,
  SanityCheck,
  ProblemStateLib,
  ProblemLib,
  CurrentStep,
  MemoryCellLib,
  FindIndicesLib,
  DeduceLib,
  ConstrainsLib,
  IfLib,
  PublicationLib,
  LambdaLib,
  FaLib,
  SubstLib,
  VampireLib,
  NonceLib,
);
