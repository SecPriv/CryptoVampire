// use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Rewrite, Runner,
    StopReason,
};
use itertools::{Either, Itertools};
use log::info;
use rule::PlOrRw;
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Display,
    mem,
    rc::Rc,
    str::FromStr,
    usize,
};
use utils::implvec;

mod eclassmap;
mod rule;
pub use rule::{Dependancy, Fresh, PrologRule, Rule};
// mod language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Status {
    True,
    False,
    InProgress,
}

mod simplify_and;
pub use simplify_and::{and_simpl_rewrite, WithAnd, WithTrue};

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

impl<L: Language + Display, N: Analysis<L> + Default> Program<L, N> {
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

    pub fn set_memo(&mut self, activated:bool) -> bool {
        let set = self.memo.is_some() == activated;
        if !set {
            self.memo = activated.then(Default::default)
        }
        set
    }

    pub fn reset_memo(&mut self) {
        self.memo = self.memo.is_some().then(Default::default)
    }

    pub fn run_expr(&mut self, goal: RecExpr<L>, depth: u128) -> bool {
        let goal = self.egraph.as_mut().unwrap().add_expr(&goal);
        self.run_egraph();
        self.run(goal, depth)
    }

    pub fn run(&mut self, goal: egg::Id, depth: u128) -> bool {
        if self.config.trace_prolog {
            let g = self.egraph().id_to_expr(goal);
            eprintln!("({depth:}) {}", g.pretty(80))
        }

        if depth == 0 {
            if self.config.trace_prolog {
                eprintln!("❌ ran out of fuel")
            }
            return false;
        }

        let memo = if let Some(memo) = self.memo_mut() {
            use std::collections::hash_map::Entry;
            match memo.entry(goal) {
                Entry::Occupied(occupied_entry) => {
                    let res = occupied_entry.get().borrow().as_bool();
                    if self.config.trace_prolog {
                        eprintln!("⏩ skipping: {:}", res)
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
            // self.rules may change during the search, hence why we can't use iterators
            let Some(r) = self.rules.get(i).cloned() else {
                break false; // no more path to a proof
            };
            i += 1;
            let search = r.search(self, goal);
            self.run_egraph();
            let ret = search
                .inner()
                .iter()
                .any(|goals| goals.iter().all(|g| self.run(*g, depth - 1)));
            if ret || search.cut() {
                break ret; // found a proof or cut
            }
        };
        if let Some(memo) = memo {
            *memo.borrow_mut() = ret.into();
        }
        ret
    }

    pub fn add_expr(&mut self, e: &RecExpr<L>) -> Id {
        match &mut self.egraph {
            Some(egraph) => egraph.add_expr(e),
            None => panic!("invalid program"),
        }
    }

    pub fn run_egraph(&mut self) {
        let mut egraph = self.egraph.take().expect("invalid program");
        if !egraph.clean {
            if self.config.trace_prolog {
                eprintln!("🚧 rebuilding egraph...");
            }
            let runner = self
                .config
                .apply(Runner::<L, N>::new(Default::default()))
                .with_egraph(egraph)
                .run(&self.eq_rules);

            let total_time = runner.report().total_time;

            if !matches!(
                &runner.stop_reason,
                Some(StopReason::Saturated) | Some(StopReason::IterationLimit(_))
            ) {
                // runner.egraph.dot().to_pdf("/tmp/out.pdf");
                eprintln!("!!!! unclean graph: {:?}", runner.stop_reason)
            }

            egraph = runner.egraph;
            // self.memo.canonicalise(&egraph);
            if self.config.trace_prolog && self.memo.is_some() {
                eprintln!("🚧 canonicalising table...");
            }
            {
                let memo = std::mem::take(&mut self.memo);
                self.memo =
                    memo.map(|x| x.into_iter().map(|(id, s)| (egraph.find(id), s)).collect());
            }
            if self.config.trace_prolog {
                eprintln!("✅ rebuilding done ! ({total_time:})");
            }
        }
        self.egraph = Some(egraph);
        assert!(self.clean());
    }

    pub fn egraph(&self) -> &EGraph<L, N> {
        self.egraph.as_ref().expect("invalid program")
    }
    pub fn egraph_mut(&mut self) -> &mut EGraph<L, N> {
        self.egraph.as_mut().expect("invalid program")
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
    L: Language + Sync + Send + FromOp + Fresh + Display + 'static,
    N: WeightedAnalysis<L> + Default,
    anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
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
