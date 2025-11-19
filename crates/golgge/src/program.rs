#[cfg(feature = "sync")]
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::ops::Deref;
#[cfg(feature = "sync")]
use std::ops::DerefMut;
use std::path::PathBuf;
use std::rc::Rc;
use std::str::FromStr;
#[cfg(feature = "sync")]
use std::sync::{Arc, RwLock};

use bon::bon;
use colored::{ColoredString, Colorize};
// use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Report, Rewrite,
    Runner, StopReason,
};
use itertools::{Either, Itertools};
use log::trace;
use serde::Serialize;
use utils::implvec;

use crate::proof::{Proof, SearchResult};
// use crate::rule::PlOrRw;
use crate::{Config, DRule, DebugLevel, Dependancy, Fresh, ProofItem, Rule, WeightedAnalysis};

/// A program that manages an `egg::EGraph` and a set of rules.
/// A program that manages an `egg::EGraph` and a set of rules.
pub struct Program<L: Language, N: Analysis<L>, R = DRule<L, N>> {
    /// The underlying e-graph.
    egraph: Option<EGraph<L, N>>,
    /// Equality rewrite rules.
    eq_rules: Vec<Rewrite<L, N>>,
    /// Custom rules.
    rules: Vec<R>,
    /// Memoization table for proof attempts.
    memo: Option<HashMap<Id, MemoStatus<R>>>,
    /// Indicates if the program is in a clean state.
    clean: bool,
    /// Configuration for the program.
    pub config: Config,
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

/// A wrapper around `Rc<RefCell<Status<L, N>>>` for memoization.
/// A wrapper around `Rc<RefCell<Status<L, N>>>` for memoization.
#[cfg(feature = "sync")]
pub(crate) struct MemoStatus<R>(Arc<RwLock<Status<R>>>);
#[cfg(not(feature = "sync"))]
pub(crate) struct MemoStatus<R>(Rc<RefCell<Status<R>>>);

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
        #[builder(default = true)] with_memo: bool,
        #[builder(default)] config: Config,
    ) -> Self {
        Self {
            egraph: Some(egraph),
            eq_rules,
            rules: rules.into_iter().map_into().collect(),
            memo: with_memo.then(Default::default),
            clean: true,
            config,
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
    ///
    /// deactivating it, then reactivating it resets it
    /// Activates or deactivates memoization/tabling.
    ///
    /// Deactivating it, then reactivating it resets it.
    pub fn set_memo(&mut self, activated: bool) -> bool {
        let set = self.memo.is_some() == activated;
        if !set {
            self.memo = activated.then(Default::default)
        }
        set
    }

    /// Resets the memoization table.
    pub fn reset_memo(&mut self) {
        self.memo = self.memo.is_some().then(Default::default)
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

    fn memo_mut(&mut self) -> Option<&mut HashMap<Id, MemoStatus<R>>> {
        self.memo.as_mut()
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

    /// same as [Self::run_expr] but starting from an [Id] in the [EGraph]
    pub fn run(&mut self, goal: egg::Id, depth: u64) -> bool {
        let gtmp = if self.is_tracing_enabled(DebugLevel::RULE) {
            let g = self.egraph().id_to_expr(goal);
            println!("{}:{}:{}", file!(), line!(), column!());
            println!("({goal:}) {}", g.pretty(80));
            Some(g)
        } else {
            None
        };

        if depth == 0 {
            mtrace!(self, RULE, "❌ ran out of fuel");
            return false;
        }

        // check memoization
        let memo = if let Some(memo) = self.memo_mut() {
            use std::collections::hash_map::Entry;
            match memo.entry(goal) {
                Entry::Occupied(occupied_entry) if occupied_entry.get().is_in_progress() => {
                    mtrace!(self, RULE, "⏩ skipping: {}", "loop".red());
                    return false;
                }
                Entry::Occupied(occupied_entry) => {
                    let res = occupied_entry.get().as_bool();
                    mtrace!(self, RULE, "⏩ skipping: {}", print_bool(res));
                    return res;
                }
                Entry::Vacant(vacant_entry) => Some(vacant_entry.insert(Status::InProgress.into())),
            }
        } else {
            None
        }
        .cloned();

        // this is a `for` loop but
        // self.rules may change during the search, hence why we can't use iterators
        let mut i = 0;
        let proof = loop {
            let Some(r) = self.rules.get(i).cloned() else {
                break None; // no more path to a proof
            };
            i += 1;

            let search = r.search(self, goal);

            if !search.is_impossible() {
                mtrace!(self, RULE, "matched rule '{}'", r.name());
            }

            let cut = search.cut();
            self.rebuild();

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
                )
            }

            let ret = search
                .inner()
                .iter()
                .position(|goals| goals.iter().all(|g| self.run(*g, depth - 1)))
                .map(|i| {
                    let Dependancy { inner, payload, .. } = search;
                    ProofItem {
                        rule: r.clone(),
                        ids: inner[i].clone(),
                        payload,
                    }
                });
            if ret.is_some() || cut {
                break ret; // found a proof or cut
            }
        };

        let result = proof.is_some();

        // save memoisation
        if let Some(memo) = memo {
            memo.set(if let Some(proof) = proof {
                Status::True(proof)
            } else {
                Status::False
            })
        }

        if let Some(g) = gtmp {
            mtrace!(
                self,
                RULE,
                "({goal:}) 💾 setting {} to {}",
                g.pretty(80),
                print_bool(result)
            )
        }
        result
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
        if self.memo.is_some() {
            mtrace!(self, REBUILDS, "🚧 canonicalising table...");

            let memo = std::mem::take(&mut self.memo);
            self.memo = memo.map(|x| x.into_iter().map(|(id, s)| (egraph.find(id), s)).collect());

            mtrace!(self, REBUILDS, "✅ done!");
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
    }

    pub fn get_proof_item(&self, id: Id) -> Option<ProofItem<R>> {
        self.memo.as_ref()?.get(&id)?.get_proof()
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

    pub fn get_proof(&self) -> Option<ProofItem<R>>
    where
        R: Clone,
    {
        match self.borrow().deref() {
            Status::True(proof_item) => Some(proof_item.clone()),
            _ => None,
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
