use std::fmt::{Debug, Display};
use std::path::PathBuf;
// use std::str::FromStr;

use anyhow::{Context, anyhow, ensure};
use bon::bon;
use colored::{ColoredString, Colorize};
// use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Report, Rewrite,
    Runner, StopReason,
};
// use itertools::{Either, Itertools};
use itertools::Itertools;
use log::trace;
use serde::Serialize;
use utils::implvec;

use crate::proof::SearchResult;
// use crate::rule::PlOrRw;
use crate::analysis::erase;
use crate::{
    BeginResult, Config, DRule, DebugLevel, Dependancy, Flags, Fresh, HasMemo, MemoKind, ProofItem,
    Rule, canonicalize_id_mut,
};

/// A program that manages an `egg::EGraph` and a set of rules.
#[non_exhaustive]
pub struct Program<L: Language, N: Analysis<L>, R = DRule<L, N>> {
    /// The underlying e-graph.
    egraph: Option<EGraph<L, N>>,
    /// Equality rewrite rules.
    eq_rules: Vec<Rewrite<L, N>>,
    /// Custom rules.
    rules: Vec<R>,
    /// Indicates if the program is in a clean state.
    clean: bool,
    /// Configuration for the program.
    pub config: Config,

    /// Number of time the memoisation was hit
    num_memo_hits: u64,

    /// number of times `run` was called
    total_calls: u64,
}

#[bon]
impl<L, N, R> Program<L, N, R>
where
    L: Language,
    N: Analysis<L>,
{
    /// Creates a new `Program` instance.
    #[builder]
    pub fn build(
        egraph: EGraph<L, N>,
        #[builder(with = <_>::from_iter, default = vec![])] eq_rules: Vec<Rewrite<L, N>>,
        // #[builder(with = |rules: impl IntoIterator<Item = I>| rules.into_iter().map_into().collect(), default = vec![])]
        #[builder(with = <_>::from_iter, default = vec![])] rules: Vec<R>,
        #[builder(default)] config: Config,
    ) -> Self {
        Self {
            egraph: Some(egraph),
            eq_rules,
            rules: rules.into_iter().map_into().collect(),
            clean: true,
            config,
            num_memo_hits: 0,
            total_calls: 0,
        }
    }

    /// Get the underlying [`EGraph`]
    ///
    /// ### panic
    /// If the egraph was taken. This should not happen outside of internal
    /// function
    pub fn egraph(&self) -> &EGraph<L, N> {
        self.egraph.as_ref().expect("invalid program")
    }

    /// Mutably get the underlying [`EGraph`]
    ///
    /// see [Self::egraph]
    pub fn egraph_mut(&mut self) -> &mut EGraph<L, N> {
        self.egraph.as_mut().expect("invalid program")
    }

    /// activate/deactivate memoisation/tabling
    pub fn set_memo(&mut self, activated: bool) {
        self.config.flags.set(Flags::MEMOIZATION, activated);
    }

    /// Is memoisation enabled ?
    #[inline]
    pub fn is_memo_enabled(&self) -> bool {
        self.config.flags.contains(Flags::MEMOIZATION)
    }

    /// adds `e` to the egraph
    /// Adds an expression to the e-graph.
    pub fn add_expr(&mut self, e: &RecExpr<L>) -> Id {
        match &mut self.egraph {
            Some(egraph) => egraph.add_expr(e),
            None => panic!("invalid program"),
        }
    }

    /// is the program in a clean state?
    ///
    /// The program is clean when it has an [EGraph] and that [EGraph] is clean
    pub fn clean(&self) -> bool {
        self.clean
            && if let Some(eg) = self.egraph.as_ref() {
                eg.clean
            } else {
                eprintln!("no egraph!");
                false
            }
    }

    /// Add rewrite rules, and [Rule]s
    /// Adds rewrite rules and `Rule`s to the program.
    pub fn extend(&mut self, eq_rules: implvec!(Rewrite<L, N>), rules: implvec!(R)) {
        self.eq_rules.extend(eq_rules);
        self.rules.extend(rules.into_iter().map_into());
    }

    /// add rewrite rules
    /// Adds a single rewrite rule to the program.
    pub fn add_eq_rule(&mut self, eq_rule: Rewrite<L, N>) {
        self.extend([eq_rule], []);
    }

    /// activate/deactivate explaination for the [EGraph]
    ///
    /// refer to [egg]'s documentation to know more
    pub fn set_explainations(&mut self, explaination: bool) {
        let egraph = self.egraph.take().expect("invalid");
        let egraph = if explaination {
            egraph.with_explanations_enabled()
        } else {
            egraph.with_explanations_disabled()
        };
        self.egraph = Some(egraph)
    }

    /// Returns a slice of the equality rewrite rules.
    pub fn eq_rules(&self) -> &[Rewrite<L, N>] {
        &self.eq_rules
    }

    /// clears the rules and returns the old one following the semantics of [`std::mem::take`]
    pub fn take_eq_rules(&mut self) -> Vec<Rewrite<L, N>> {
        self.eq_rules.clear();
        ::std::mem::take(&mut self.eq_rules)
    }

    /// Sets the equality rewrite rules.
    #[cfg(debug_assertions)]
    pub fn set_eq_rules(&mut self, new: Vec<Rewrite<L, N>>)
    where
        L: Display,
    {
        self.egraph_mut().clean = false;
        self.eq_rules = new;

        #[cfg(debug_assertions)]
        {
            for r in &self.eq_rules {
                println!("{r:?}")
            }
        }
    }

    /// Sets the equality rewrite rules.
    #[cfg(not(debug_assertions))]
    pub fn set_eq_rules(&mut self, new: Vec<Rewrite<L, N>>) {
        self.egraph_mut().clean = false;
        self.eq_rules = new;
    }

    /// Returns a slice of the `Rule`s.
    pub fn rules(&self) -> &[R] {
        &self.rules
    }

    /// Returns `true` if tracing is enabled.
    #[inline]
    pub const fn is_tracing_enabled(&self, kind: DebugLevel) -> bool {
        kind.intersects(self.config.trace)
    }

    pub fn get_memo_hit(&self) -> u64 {
        self.num_memo_hits
    }

    pub fn get_num_calls(&self) -> u64 {
        self.total_calls
    }

    /// Rate at which the memoisation kicks in
    pub fn get_hit_rate(&self) -> f64 {
        (self.num_memo_hits as f64) / (self.total_calls as f64)
    }
}

/// Forgets the memoization result of a single e-class, resetting its cell back
/// to `Unknown`.
impl<L, N, R> Program<L, N, R>
where
    L: Language,
    N: Analysis<L>,
    N::Data: HasMemo,
{
    pub fn forget(&mut self, id: Id) {
        if self.is_memo_enabled() {
            self.egraph_mut()[id].data.memo_mut().clear();
        }
    }
}

fn print_bool(b: bool) -> ColoredString {
    match b {
        true => "true".green(),
        false => "false".red(),
    }
}

impl<L, N, R> Program<L, N, R>
where
    L: Language + Display,
    N: Analysis<L>,
    R: Rule<L, N, R> + Clone,
{
    /// Debug the available [`Rule`]s by calling [Rule::debug]
    pub fn debug_rules(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        for r in self.eq_rules() {
            writeln!(f, "{r:?}")?;
        }

        for r in &self.rules {
            r.debug(f)?;
            writeln!(f)?;
        }
        Ok(())
    }

    /// Alternative debug method based on [Self::debug_rules] to leave [Debug]
    /// clean
    pub fn as_debug_rules(&self) -> impl Debug {
        struct DP<'a, L: Language, N: Analysis<L>, R>(&'a Program<L, N, R>);
        impl<'a, L: Language + Display, N: Analysis<L>, R: Rule<L, N, R> + Clone> Debug
            for DP<'a, L, N, R>
        {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.debug_rules(f)
            }
        }
        DP(self)
    }
}

impl<L, N, R> Program<L, N, R>
where
    L: Language + Display,
    N: Analysis<L>,
    N::Data: HasMemo,
    R: Rule<L, N, R> + Clone + 'static + Send + Sync,
{
    /// Try to prove `goal` going a most `depth` deep
    pub fn run_expr(&mut self, goal: RecExpr<L>, depth: u64) -> SearchResult {
        mtrace!(self, RULE, "{:?}", self.as_debug_rules());

        let goal = self.egraph.as_mut().unwrap().add_expr(&goal);
        self.rebuild();
        match self.run(goal, depth) {
            true => SearchResult::True(goal),
            false => SearchResult::False,
        }
    }

    /// same as [Self::run_expr] but starting from an [Id] in the [EGraph]
    pub fn run(&mut self, base_goal: egg::Id, fuel: u64) -> bool {
        self.total_calls += 1;
        let gtmp = if self.is_tracing_enabled(DebugLevel::RULE) {
            let g = self.egraph().id_to_expr(base_goal);
            println!("({base_goal:}) selecting {}", g.pretty(80));
            Some(g)
        } else {
            None
        };

        if fuel == 0 {
            mtrace!(self, RULE, "❌ ran out of fuel");
            return false;
        }

        // this is a `for` loop but
        // self.rules may change during the search, hence why we can't use iterators
        let mut i = 0;
        let mut goal = base_goal;
        let proof = loop {
            #[cfg(debug_assertions)]
            self.check_proof_consistency().unwrap();

            let canonicalized = canonicalize_id_mut(&mut goal, self.egraph());
            // check / start memoization
            if self.is_memo_enabled() && (canonicalized || i == 0) {
                if let Some(res) = self.memo_check_or_start(goal) {
                    // yes side effects ^^', this is here because I don't
                    // want break out of a loop that came from a rewrite mid proof
                    if i == 0 {
                        return res;
                    } else {
                        mtrace!(self, RULE, "not skipping !!!!!")
                    }
                }
            }

            let Some(r) = self.rules.get(i).cloned() else {
                break None; // no more path to a proof
            };
            i += 1;

            trace!("({base_goal:}) rule: '{}'", r.name());

            let search = r.search(self, goal);

            if !search.is_impossible() {
                mtrace!(self, RULE, "matched rule '{}'", r.name());
            }

            let cut = search.cut();
            self.rebuild();

            if self.is_tracing_enabled(DebugLevel::RULE) && !search.is_impossible() {
                self.trace_goal_status(goal, &search);
            }

            let ret = search
                .inner()
                .iter()
                .position(|goals| goals.iter().all(|g| self.run(*g, fuel - 1)))
                .map(|i| {
                    let Dependancy { inner, payload, .. } = search;

                    let mut ids = inner[i].clone();
                    for id in &mut ids {
                        canonicalize_id_mut(id, self.egraph());
                    }

                    ProofItem {
                        rule: r.clone(),
                        ids,
                        payload,
                    }
                });
            if ret.is_some() || cut {
                break ret; // found a proof or cut
            }
        };

        canonicalize_id_mut(&mut goal, self.egraph());
        let result = proof.is_some();
        // save memoisation
        if self.is_memo_enabled() {
            self.memo_set_result(goal, proof);
        }

        if let Some(g) = gtmp {
            mtrace!(
                self,
                RULE,
                "({goal:}) 💾 setting {} to {}",
                g.pretty(80),
                print_bool(result)
            );
        }

        #[cfg(debug_assertions)]
        self.check_proof_consistency().unwrap();

        result
    }

    /// Reads the memo cell of `goal` and, if it already holds a terminal result,
    /// returns it (counting a cache hit). Otherwise marks the cell as
    /// `InProgress` and returns `None` so the search can proceed.
    fn memo_check_or_start(&mut self, goal: Id) -> Option<bool> {
        match self.egraph_mut()[goal].data.memo_mut().begin_search() {
            BeginResult::Started => None,
            BeginResult::Cached(res) => {
                self.num_memo_hits += 1;
                mtrace!(self, RULE, "⏩ skipping {goal:}: {}", print_bool(res));
                Some(res)
            }
            BeginResult::Cycle => {
                mtrace!(self, RULE, "⏩ skipping {goal:}: {}", "loop".red());
                Some(false)
            }
        }
    }

    /// Records the terminal result of a proof attempt for `goal`, applying the
    /// merge lattice (so a `Failed` never overwrites a `Proven`, etc.).
    fn memo_set_result(&mut self, goal: Id, proof: Option<ProofItem<R>>) {
        let cell = self.egraph_mut()[goal].data.memo_mut();
        match proof {
            Some(item) => {
                cell.set_proven(erase(item));
            }
            None => {
                cell.set_failed();
            }
        }
    }

    fn trace_goal_status(&self, goal: Id, search: &Dependancy) {
        mtrace!(
            self,
            RULE,
            "({goal}) new goals\n{}",
            search
                .inner
                .iter()
                .map(|d| format!(
                    "\t - [{}]",
                    d.iter()
                        .map(|c| format!("({})", self.egraph().find(*c)))
                        .join(", ")
                ))
                .join("\n")
        );

        if cfg!(debug_assertions) {
            eprintln!("({goal}) new goals prefetch:");

            for d in search.inner.iter() {
                eprint!("\t - [");
                for c in d {
                    match self.egraph()[*c].data.memo().kind() {
                        MemoKind::Failed => eprint!("{c} ({})", "false".red()),
                        MemoKind::Proven => eprint!("{c} ({})", "true".green()),
                        MemoKind::InProgress => eprint!("{c} ({})", "loop".red()),
                        MemoKind::Unknown => eprint!("{c} (?)"),
                    }
                    eprint!(", ")
                }
                eprintln!("]");
            }
        }
    }

    /// Rebuild the [EGraph] according the set of rules defined by `rules` and
    /// update all the relevant datastructures
    ///
    /// - If `rules` is empty then this uses [Self::eq_rules]
    /// - this is where [Rule::rebuild] is called
    pub fn run_rw_rules(&mut self, rules: Option<&[Rewrite<L, N>]>) -> Report {
        let mut egraph = self.egraph.take().expect("invalid program");
        mtrace!(self, REBUILDS, "🚧 rebuilding egraph...");
        let size = egraph.number_of_classes();

        let runner = self
            .config
            .apply(Runner::<L, N>::new_with_egraph(egraph))
            .run(rules.unwrap_or(self.eq_rules()));

        let report = runner.report();

        mtrace!(self, REBUILDS, "✅ done !\n{report}");

        egraph = runner.egraph;

        self.egraph = Some(egraph);

        {
            mtrace!(self, REBUILDS, "🚧 canonicalising rules...");
            self.rules.iter().for_each(|r| r.rebuild(self));
            mtrace!(self, REBUILDS, "✅ done!");
        }
        assert!(self.clean());

        if cfg!(debug_assertions) && self.egraph().number_of_classes() >= size + (size / 8) {
            eprintln!("\n\t!!! large increase !!!\t\n");
        }
        report
    }

    /// Checks that every `Proven` cell's subgoals are themselves `Proven`.
    pub fn check_proof_consistency(&self) -> anyhow::Result<()> {
        if self.is_memo_enabled() {
            for class in self.egraph().classes() {
                let cell = class.data.memo();
                if !matches!(cell.kind(), MemoKind::Proven) {
                    continue;
                }
                let Some(erased) = cell.proof_ref() else {
                    continue;
                };
                let Some(item) = erased.as_ref().downcast_ref::<ProofItem<R>>() else {
                    continue;
                };
                for id in &item.ids {
                    let child = self.egraph()[*id].data.memo();
                    ensure!(
                        matches!(child.kind(), MemoKind::Proven),
                        "{id} parent of {} isn't proven",
                        class.id
                    );
                }
            }
        }
        Ok(())
    }

    /// rebuilds self
    pub fn rebuild(&mut self) {
        if !self.egraph().clean {
            let report = self.run_rw_rules(None);
            let stop_reason = report.stop_reason.clone();
            if !matches!(stop_reason, StopReason::Saturated) {
                let dot = save_egraph(self.egraph()).unwrap();
                panic!("unclean graph. See {dot:?}")
            }
        }
        assert!(self.clean());

        #[cfg(debug_assertions)]
        self.check_proof_consistency().unwrap();
    }

    /// Retrieves the [`ProofItem`] recorded for `id`.
    ///
    /// Requires memoisation to be enabled and `id` to have been proven.
    pub fn get_proof_item(&self, id: Id) -> anyhow::Result<ProofItem<R>> {
        ensure!(self.is_memo_enabled(), "memoisation disabled");
        let cell = self.egraph()[id].data.memo();
        match cell.kind() {
            MemoKind::Proven => {
                let erased = cell.proof_ref().with_context(|| "inconsistent memo cell")?;
                let item = erased
                    .as_ref()
                    .downcast_ref::<ProofItem<R>>()
                    .with_context(|| "memo cell holds a different proof type")?
                    .clone();
                Ok(item)
            }
            MemoKind::Failed => Err(anyhow!("goal {id} is false")),
            MemoKind::InProgress => Err(anyhow!("goal {id} in progress")),
            MemoKind::Unknown => Err(anyhow!("goal {id} hasn't been memoized")),
        }
    }
}

// impl<L, N, R> FromStr for Program<L, N, R>
// where
//     L: Language + Sync + Send + FromOp + Fresh + Display + 'static + Serialize,
//     N: WeightedAnalysis<L> + Default + Serialize,
//     anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
//     anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
//     N::Data: Serialize,
//     R: From<PrologRule<L>>
// {
//     /// The error type returned when parsing fails.
//     type Err = anyhow::Error;
//
//     /// Parses a string into a `Program`.
//     fn from_str(s: &str) -> Result<Self, Self::Err> {
//         let (rules, eq_rules) = PlOrRw::parse_program(s)?
//             .into_iter()
//             .partition_map(|p| match p {
//                 PlOrRw::Pl(prolog_rule) => {
//                     // let b: Box<dyn Rule<L, N>> = Box::new(prolog_rule);
//                     Either::Left(prolog_rule.into())
//                 }
//                 PlOrRw::Rw(rewrite) => Either::Right(rewrite),
//             });
//         Ok(Self {
//             egraph: Some(Default::default()),
//             eq_rules,
//             rules,
//             clean: true,
//             config: Default::default(),
//         })
//     }
// }

/// Saves the e-graph to a DOT file in a temporary location.
fn save_egraph<L, N>(egraph: &EGraph<L, N>) -> std::io::Result<PathBuf>
where
    L: Language + Display,
    N: Analysis<L>,
{
    let dot = tempfile::Builder::new()
        .prefix("egraph_")
        .suffix(".dot")
        .disable_cleanup(true)
        .tempfile()?;

    egraph.dot().to_dot(&dot)?;

    Ok(dot.path().to_path_buf())
}
