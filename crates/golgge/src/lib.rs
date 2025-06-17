use bon::{bon, builder};
// use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Rewrite, Runner,
    StopReason,
};
use itertools::{Either, Itertools};
use log::log_enabled;
use rule::PlOrRw;
use serde::Serialize;
use std::{
    cell::RefCell,
    collections::HashMap,
    default,
    fmt::{Debug, Display},
    path::PathBuf,
    rc::Rc,
    str::FromStr,
};
use utils::implvec;

// mod eclassmap;
mod rule;
pub use rule::{DebugRule, Dependancy, Fresh, PrologRule, Rule};
// mod language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Status {
    True,
    False,
    InProgress,
}

mod simplify_and;
pub use simplify_and::{WithAnd, WithTrue, and_simpl_rewrite};

mod weight;
pub use weight::MWeight;

mod analysis;
pub use analysis::{MAnalysis, WeightedAnalysis};

pub struct Program<L: Language, N: Analysis<L>> {
    egraph: Option<EGraph<L, N>>,
    eq_rules: Vec<Rewrite<L, N>>,
    rules: Vec<Rc<dyn Rule<L, N>>>,
    // memo: ECallMap<Rc<RefCell<Status>>>,
    memo: Option<HashMap<Id, Rc<RefCell<Status>>>>,
    clean: bool,
    pub config: Config,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct Config {
    pub iter_limit: usize,
    pub node_limit: usize,
    pub time_limit: std::time::Duration,
    pub trace_prolog: bool,
}

impl Config {
    pub fn apply<L: Language, N: Analysis<L>>(&self, runner: Runner<L, N>) -> Runner<L, N> {
        runner
            .with_iter_limit(self.iter_limit)
            .with_node_limit(self.node_limit)
            .with_time_limit(self.time_limit)
    }
}

impl Default for Config {
    fn default() -> Self {
        Self {
            iter_limit: 150,
            node_limit: 1000,
            time_limit: std::time::Duration::from_secs(5),
            trace_prolog: cfg!(debug_assertions),
        }
    }
}

#[bon]
impl<L, N> Program<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    #[builder]
    pub fn build(
        egraph: EGraph<L, N>,
        #[builder(with = <_>::from_iter, default = vec![])] eq_rules: Vec<Rewrite<L, N>>,
        // #[builder(with = |rules: impl IntoIterator<Item = I>| rules.into_iter().map_into().collect(), default = vec![])]
        #[builder(with = <_>::from_iter, default = vec![])]
        rules: Vec<Rc<dyn Rule<L, N>>>,
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

    pub fn egraph(&self) -> &EGraph<L, N> {
        self.egraph.as_ref().expect("invalid program")
    }
    pub fn egraph_mut(&mut self) -> &mut EGraph<L, N> {
        self.egraph.as_mut().expect("invalid program")
    }

    pub fn debug_rules(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        for r in &self.rules {
            r.debug(f)?;
            writeln!(f)?;
        }
        Ok(())
    }
}

impl<L, N> Program<L, N>
where
    L: Language + Display,
    N: Analysis<L>,
{
    pub fn new(
        egraph: EGraph<L, N>,
        eq_rules: implvec!(Rewrite<L, N>),
        rules: implvec!(Box<dyn Rule<L, N>>),
        with_memo: bool,
    ) -> Self {
        Self {
            egraph: Some(egraph),
            eq_rules: eq_rules.into_iter().collect(),
            rules: rules.into_iter().map_into().collect(),
            memo: with_memo.then(Default::default),
            clean: true,
            config: Default::default(),
        }
    }

    pub fn set_memo(&mut self, activated: bool) -> bool {
        let set = self.memo.is_some() == activated;
        if !set {
            self.memo = activated.then(Default::default)
        }
        set
    }

    pub fn reset_memo(&mut self) {
        self.memo = self.memo.is_some().then(Default::default)
    }

    pub fn add_expr(&mut self, e: &RecExpr<L>) -> Id {
        match &mut self.egraph {
            Some(egraph) => egraph.add_expr(e),
            None => panic!("invalid program"),
        }
    }

    pub fn clean(&self) -> bool {
        self.clean
            && if let Some(eg) = self.egraph.as_ref() {
                eg.clean
            } else {
                eprintln!("no egraph!");
                false
            }
    }

    pub fn extend(
        &mut self,
        eq_rules: implvec!(Rewrite<L, N>),
        rules: implvec!(Box<dyn Rule<L, N>>),
    ) {
        self.eq_rules.extend(eq_rules);
        self.rules.extend(rules.into_iter().map_into());
    }

    pub fn add_eq_rule(&mut self, eq_rule: Rewrite<L, N>) {
        self.extend([eq_rule], []);
    }

    pub fn add_boxed_rule(&mut self, rule: Box<dyn Rule<L, N>>) {
        self.extend([], [rule]);
    }

    pub fn add_rule<R: Rule<L, N> + 'static>(&mut self, rule: R) {
        self.add_boxed_rule(Box::new(rule))
    }

    pub fn set_explainations(&mut self, explaination: bool) {
        let egraph = self.egraph.take().expect("invalid");
        let egraph = if explaination {
            egraph.with_explanations_enabled()
        } else {
            egraph.with_explanations_disabled()
        };
        self.egraph = Some(egraph)
    }

    fn memo_mut(&mut self) -> Option<&mut HashMap<Id, Rc<RefCell<Status>>>> {
        self.memo.as_mut()
    }

    pub fn eq_rules(&self) -> &[Rewrite<L, N>] {
        &self.eq_rules
    }

    pub fn rules(&self) -> &[Rc<dyn Rule<L, N>>] {
        &self.rules
    }
    // }

    // impl<L, N> Program<L, N>
    // where
    //     L: Language + Display + Serialize,
    //     N: Analysis<L> + Default + Serialize,
    //     N::Data: Serialize,
    // {
    pub fn run_expr(&mut self, goal: RecExpr<L>, depth: u128) -> bool {
        if cfg!(debug_assertions) {
            struct DP<'a, L: Language, N: Analysis<L>>(&'a Program<L, N>);
            impl<'a, L: Language, N: Analysis<L>> Debug for DP<'a, L, N> {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    self.0.debug_rules(f)
                }
            }
            eprintln!("{:?}", DP(self))
        }

        let goal = self.egraph.as_mut().unwrap().add_expr(&goal);
        self.rebuild();
        self.run(goal, depth)
    }

    pub fn run(&mut self, goal: egg::Id, depth: u128) -> bool {
        let gtmp = if self.config.trace_prolog {
            let g = self.egraph().id_to_expr(goal);
            eprintln!("({depth:}) {}", g.pretty(80));
            Some(g)
        } else {
            None
        };

        if depth == 0 {
            if self.config.trace_prolog {
                eprintln!("❌ ran out of fuel")
            }
            return false;
        }

        // check memoization
        let memo = if let Some(memo) = self.memo_mut() {
            use std::collections::hash_map::Entry;
            match memo.entry(goal) {
                Entry::Occupied(occupied_entry) => {
                    let res = occupied_entry.get().borrow().as_bool();
                    if self.config.trace_prolog {
                        eprintln!("⏩ skipping: {res:}")
                    }
                    return res;
                }
                Entry::Vacant(vacant_entry) => {
                    Some(vacant_entry.insert(Rc::new(RefCell::new(Status::InProgress))))
                }
            }
        } else {
            None
        }
        .cloned();

        let mut i = 0;
        let ret = loop {
            // this is a `for` loop but
            // self.rules may change during the search, hence why we can't use iterators
            let Some(r) = self.rules.get(i).cloned() else {
                break false; // no more path to a proof
            };
            i += 1;
            let search = r.search(self, goal);
            self.rebuild();
            let ret = search
                .inner()
                .iter()
                .any(|goals| goals.iter().all(|g| self.run(*g, depth - 1)));
            if ret || search.cut() {
                break ret; // found a proof or cut
            }
        };

        // save memoisation
        if let Some(memo) = memo {
            *memo.borrow_mut() = ret.into();
        }

        if let Some(g) = gtmp {
            eprintln!("({depth:}) {} -> {ret}", g.pretty(80))
        }
        ret
    }

    pub fn rebuild(&mut self) {
        let mut egraph = self.egraph.take().expect("invalid program");
        if !egraph.clean {
            if self.config.trace_prolog {
                eprintln!("🚧 rebuilding egraph...");
            }
            let runner = self
                .config
                .apply(Runner::<L, N>::new_with_egraph(egraph))
                // .with_egraph(egraph)
                .run(&self.eq_rules);

            let report = runner.report();

            if self.config.trace_prolog {
                eprintln!("✅ done !\n{report}");
            }

            let stop_reason = runner.stop_reason.clone();

            egraph = runner.egraph;

            if !matches!(stop_reason, Some(StopReason::Saturated)) {
                let dot = save_egraph(&egraph).unwrap();
                panic!("unclean graph. See {dot:?}")
            }

            // self.memo.canonicalise(&egraph);
            if self.memo.is_some() {
                if self.config.trace_prolog {
                    eprintln!("🚧 canonicalising table...");
                }

                let memo = std::mem::take(&mut self.memo);
                self.memo =
                    memo.map(|x| x.into_iter().map(|(id, s)| (egraph.find(id), s)).collect());

                if self.config.trace_prolog {
                    eprintln!("✅ done!");
                }
            }

            self.egraph = Some(egraph);

            {
                if self.config.trace_prolog {
                    eprintln!("🚧 canonicalising rules...");
                }
                self.rules.iter().for_each(|r| r.rebuild(self));
                if self.config.trace_prolog {
                    eprintln!("✅ done!");
                }
            }
        } else {
            self.egraph = Some(egraph)
        }
        assert!(self.clean());
    }
}

impl Status {
    pub fn as_bool(&self) -> bool {
        matches!(self, Status::True)
    }
}

impl From<bool> for Status {
    fn from(value: bool) -> Self {
        match value {
            true => Status::True,
            false => Status::False,
        }
    }
}

impl<L, N> FromStr for Program<L, N>
where
    L: Language + Sync + Send + FromOp + Fresh + Display + 'static + Serialize,
    N: WeightedAnalysis<L> + Default + Serialize,
    anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    N::Data: Serialize,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (rules, eq_rules) = PlOrRw::parse_program(s)?
            .into_iter()
            .partition_map(|p| match p {
                PlOrRw::Pl(prolog_rule) => {
                    let b: Box<dyn Rule<L, N>> = Box::new(prolog_rule);
                    Either::Left(b.into())
                }
                PlOrRw::Rw(rewrite) => Either::Right(rewrite),
            });
        Ok(Self {
            egraph: Some(Default::default()),
            eq_rules,
            rules,
            memo: Default::default(),
            clean: true,
            config: Default::default(),
        })
    }
}

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
