#[cfg(feature = "sync")]
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
#[cfg(feature = "sync")]
use std::ops::DerefMut;
use std::ops::{ControlFlow, Deref};
use std::path::PathBuf;
use std::rc::Rc;
use std::result;
use std::str::FromStr;
#[cfg(feature = "sync")]
use std::sync::{Arc, RwLock};

use anyhow::{Context, anyhow, ensure};
use bon::bon;
use colored::{ColoredString, Colorize};
// use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Report, Rewrite,
    Runner, StopReason,
};
use itertools::{Either, Itertools};
use log::trace;
use rustc_hash::FxHashMap;
use serde::Serialize;
use utils::implvec;

use crate::proof::{Proof, SearchResult};
// use crate::rule::PlOrRw;
use crate::{
    Config, DRule, DebugLevel, Dependancy, Flags, Fresh, ProofItem, Rule, WeightedAnalysis,
    canonicalize_id, canonicalize_id_mut,
};

/// A program that manages an `egg::EGraph` and a set of rules.
/// A program that manages an `egg::EGraph` and a set of rules.
#[non_exhaustive]
pub struct Program<L: Language, N: Analysis<L>, R = DRule<L, N>> {
    /// The underlying e-graph.
    egraph: Option<EGraph<L, N>>,
    /// Equality rewrite rules.
    eq_rules: Vec<Rewrite<L, N>>,
    /// Custom rules.
    rules: Vec<R>,
    /// Memoization table for proof attempts.
    memo: FxHashMap<Id, MemoStatus<R>>,
    /// Indicates if the program is in a clean state.
    clean: bool,
    /// Configuration for the program.
    pub config: Config,

    /// Number of time the memoisation was hit
    num_memo_hits: u64,

    /// number of times `run` was called
    total_calls: u64,
}

/// Represents the status of a proof attempt for a given e-class.
#[derive(Clone)]
#[allow(dead_code)]
pub(crate) enum Status<R> {
    /// The proof attempt succeeded, containing the proof item.
    True(ProofItem<R>),
    /// The proof attempt failed.
    False,
    /// The proof attempt is currently in progress.
    InProgress,
}

pub trait Rebuildable<L: Language, N: Analysis<L>> {
    fn rebuild(&mut self, egraph: &EGraph<L, N>) {}
}

impl<L: Language, N: Analysis<L>, R> Rebuildable<L, N> for Status<R> {
    fn rebuild(&mut self, egraph: &egg::EGraph<L, N>) {
        if let Self::True(pitem) = self {
            pitem.rebuild(egraph);
        }
    }
}

/// A wrapper around `Rc<RefCell<Status<L, N>>>` for memoization.
/// A wrapper around `Rc<RefCell<Status<L, N>>>` for memoization.
#[cfg(feature = "sync")]
pub(crate) struct MemoStatus<R>(Arc<RwLock<Status<R>>>);
#[cfg(not(feature = "sync"))]
pub(crate) struct MemoStatus<R>(Rc<RefCell<Status<R>>>);

impl<L: Language, N: Analysis<L>, R> Rebuildable<L, N> for MemoStatus<R> {
    fn rebuild(&mut self, egraph: &egg::EGraph<L, N>) {
        self.0.write().unwrap().rebuild(egraph);
    }
}

impl<R> PartialEq for MemoStatus<R> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl<R> Eq for MemoStatus<R> {}

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
            memo: Default::default(),
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

    /// Resets the memoization table.
    #[deprecated]
    pub fn reset_memo(&mut self) {
        self.memo = Default::default();
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

    // /// convenient way to add a [Rule]
    // /// Adds a boxed `Rule` to the program.
    // pub fn add_boxed_rule(&mut self, rule: Box<dyn Rule<L, N>>) {
    //     self.extend([], [rule]);
    // }

    // /// convenient way to add a [Rule]
    // /// Adds a `Rule` to the program.
    // pub fn add_rule<R: Rule<L, N> + 'static>(&mut self, rule: R) {
    //     self.add_boxed_rule(Box::new(rule))
    // }

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

    fn memo_mut(&mut self) -> &mut FxHashMap<Id, MemoStatus<R>> {
        &mut self.memo
    }

    /// Returns a slice of the equality rewrite rules.
    pub fn eq_rules(&self) -> &[Rewrite<L, N>] {
        &self.eq_rules
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
    pub fn set_eq_rules(&mut self, new: Vec<Rewrite<L, N>>)
    where
        L: Display,
    {
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

    fn check_and_set_memo(&mut self, goal: egg::Id, status: Status<R>, log: bool) -> Option<bool> {
        assert!(self.is_memo_enabled());

        use std::collections::hash_map::Entry;
        match self.memo_mut().entry(goal) {
            Entry::Occupied(occupied_entry) if occupied_entry.get().is_in_progress() => {
                if log {
                    mtrace!(self, RULE, "⏩ skipping {goal:}: {}", "loop".red());
                }
                Some(false)
            }
            Entry::Occupied(occupied_entry) => {
                let res = occupied_entry.get().as_bool();
                self.num_memo_hits += 1;
                if log {
                    mtrace!(self, RULE, "⏩ skipping {goal:}: {}", print_bool(res));
                }
                Some(res)
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(status.into());
                None
            }
        }
    }

    /// same as [Self::run_expr] but starting from an [Id] in the [EGraph]
    pub fn run(&mut self, base_goal: egg::Id, fuel: u64) -> bool {
        self.total_calls += 1;
        let ndepth = u64::MAX - fuel;
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
            // check memoization
            if self.is_memo_enabled()
                && (canonicalized || i == 0)
                && let Some(res) = self.check_and_set_memo(goal, Status::InProgress, true)
            {
                // yes side effects ^^', this is here because I don't
                // want break out of a loop that came from a rewrite mid proof
                if i == 0 {
                    return res;
                } else {
                    mtrace!(self, RULE, "not skipping !!!!!")
                }
            }

            self.check_memo_goal(goal);

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
            self.check_memo_goal(goal);
            self.rebuild();
            self.check_memo_goal(goal);

            if self.is_tracing_enabled(DebugLevel::RULE) && !search.is_impossible() {
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
                            let tmp = self.memo.get(c).map(|c| c.0.read().unwrap());
                            match tmp {
                                Some(x) => match x.deref() {
                                    Status::False => eprint!("{c} ({})", "false".red()),
                                    Status::True(_) => eprint!("{c} ({})", "true".green()),
                                    Status::InProgress => eprint!("{c} ({})", "loop".red()),
                                },
                                None => eprint!("{c} (?)"),
                            }
                            eprint!(", ")
                        }
                        eprintln!("]");
                    }
                }
            }

            self.check_memo_goal(goal);

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
        self.check_and_set_memo(goal, Status::InProgress, true);

        debug_assert!(
            !self.is_memo_enabled() || self.memo.contains_key(&goal),
            "({goal:}) {}",
            self.egraph().id_to_expr(goal).pretty(100)
        );

        let result = proof.is_some();
        // save memoisation
        if self.is_memo_enabled() {
            let there = self.memo.insert(goal, Status::from(proof).into());
            assert!(
                there.is_some(),
                "the goal ({goal:}) wasn't registered at all...\nthis was {}",
                self.egraph().id_to_expr(goal).pretty(100)
            )
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

    #[inline]
    #[track_caller]
    fn check_memo_goal(&mut self, goal: Id) {
        debug_assert!(
            !self.is_memo_enabled() || self.memo.contains_key(&goal),
            "({goal:}) {}",
            self.egraph().id_to_expr(goal).pretty(100)
        );
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

        // self.memo.canonicalise(&egraph);
        if self.is_memo_enabled() {
            self.canonicalized_table(&egraph);
        }

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

    fn canonicalized_table(&mut self, egraph: &EGraph<L, N>) {
        assert!(self.is_memo_enabled());
        mtrace!(self, REBUILDS, "🚧 canonicalising table...");

        let mut memo = HashMap::with_capacity_and_hasher(self.memo.len(), Default::default());
        ::std::mem::swap(&mut self.memo, &mut memo);

        for (mut id, mut status) in memo {
            status.rebuild(egraph);
            self.update_memo_safe(id, status.clone());
            if canonicalize_id_mut(&mut id, egraph) {
                self.update_memo_safe(id, status)
            }
        }

        #[cfg(debug_assertions)]
        self.check_proof_consistency().unwrap();

        mtrace!(self, REBUILDS, "✅ done!");
    }

    fn update_memo_safe(&mut self, id: Id, status: MemoStatus<R>) {
        use ::std::collections::hash_map::Entry::*;
        match self.memo_mut().entry(id) {
            Occupied(mut entry) if !status.is_in_progress() => {
                // TODO: smarter overwrite
                entry.insert(status);
            }
            Vacant(entry) => {
                entry.insert(status);
            }
            _ => {}
        }
    }

    pub fn check_proof_consistency(&self) -> anyhow::Result<()> {
        if self.is_memo_enabled() {
            for (oid, v) in self.memo.iter() {
                let s = v.borrow();
                if let Status::True(ProofItem { ids, .. }) = s.deref() {
                    for id in ids {
                        let x = self
                            .memo
                            .get(id)
                            .with_context(|| format!("{id} parent of {oid} isn't memoized"))?;
                        ensure!(x.as_bool(), "{id} parent of {oid} is false")
                    }
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

    pub fn get_proof_item(&self, id: Id) -> anyhow::Result<ProofItem<R>> {
        ensure!(self.is_memo_enabled(), "memoisation disabled");
        let proof_item = self
            .memo
            .get(&id)
            .with_context(|| format!("goal {id} hasn't been memoized"))?
            .get_proof()
            .with_context(|| format!("for goal {id}"))?;

        // canonicalise
        // for ids in proof_item.ids.iter_mut() {
        //     *ids = self.egraph().find(*ids);
        // }
        Ok(proof_item)
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
//             memo: Default::default(),
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
        .keep(true)
        .tempfile()?;

    egraph.dot().to_dot(&dot)?;

    Ok(dot.path().to_path_buf())
}

impl<R> Status<R> {
    /// Returns `true` if the status is `True`.
    pub fn as_bool(&self) -> bool {
        matches!(self, Status::True { .. })
    }

    /// Returns `true` if the status is [`InProgress`].
    ///
    /// [`InProgress`]: Status::InProgress
    #[must_use]
    pub(crate) fn is_in_progress(&self) -> bool {
        matches!(self, Self::InProgress)
    }
}

impl<R> MemoStatus<R> {
    /// Returns `true` if the underlying `Status` is `True`.
    pub fn as_bool(&self) -> bool {
        self.borrow().as_bool()
    }

    /// Sets the underlying `Status`.
    pub fn set(&self, status: Status<R>) {
        *self.borrow_mut() = status
    }

    /// Returns `true` if the status is [`InProgress`].
    ///
    /// [`InProgress`]: Status::InProgress
    #[must_use]
    pub(crate) fn is_in_progress(&self) -> bool {
        self.borrow().is_in_progress()
    }

    pub fn get_proof(&self) -> anyhow::Result<ProofItem<R>>
    where
        R: Clone,
    {
        match self.borrow().deref() {
            Status::True(proof_item) => Ok(proof_item.clone()),
            Status::False => Err(anyhow!("goal is false")),
            Status::InProgress => Err(anyhow!("goal in progress")),
        }
    }
}

#[cfg(feature = "sync")]
impl<R> MemoStatus<R> {
    fn borrow(&self) -> impl Deref<Target = Status<R>> {
        self.0.read().unwrap()
    }

    fn borrow_mut(&self) -> impl DerefMut<Target = Status<R>> {
        self.0.write().unwrap()
    }
}

#[cfg(not(feature = "sync"))]
impl<R> MemoStatus<R> {
    fn borrow(&self) -> impl Deref<Target = Status<R>> {
        self.0.borrow()
    }

    fn borrow_mut(&self) -> impl DerefMut<Target = Status<R>> {
        self.0.borrow_mut()
    }
}

#[cfg(feature = "sync")]
impl<R> From<Status<R>> for MemoStatus<R> {
    /// Converts a `Status` into a `MemoStatus`.
    fn from(value: Status<R>) -> Self {
        Self(Arc::new(RwLock::new(value)))
    }
}

#[cfg(not(feature = "sync"))]
impl<R> From<Status<R>> for MemoStatus<R> {
    /// Converts a `Status` into a `MemoStatus`.
    fn from(value: Status<R>) -> Self {
        Self(Rc::new(RefCell::new(value)))
    }
}

impl<R> Clone for MemoStatus<R> {
    /// Clones the `MemoStatus`.
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
