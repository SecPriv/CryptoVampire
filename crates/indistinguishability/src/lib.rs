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
pub use analysis::{WeightedAnalysis, MAnalysis};

pub struct Program<L: Language, N: Analysis<L>> {
    egraph: Option<EGraph<L, N>>,
    eq_rules: Vec<Rewrite<L, N>>,
    rules: Vec<Rc<dyn Rule<L, N>>>,
    // memo: ECallMap<Rc<RefCell<Status>>>,
    memo: HashMap<Id, Rc<RefCell<Status>>>,
    clean: bool,
    pub runner_config: RunnerConfig,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[non_exhaustive]
pub struct RunnerConfig {
    pub iter_limit: usize,
    pub node_limit: usize,
    pub time_limit: std::time::Duration,
}

impl RunnerConfig {
    pub fn apply<L: Language, N: Analysis<L>>(&self, runner: Runner<L, N>) -> Runner<L, N> {
        runner
            .with_iter_limit(self.iter_limit)
            .with_node_limit(self.node_limit)
            .with_time_limit(self.time_limit)
    }
}

impl Default for RunnerConfig {
    fn default() -> Self {
        Self {
            iter_limit: 150,
            node_limit: 1000,
            time_limit: std::time::Duration::from_secs(5),
        }
    }
}

impl<L: Language + Display, N: Analysis<L> + Default> Program<L, N> {
    pub fn new(
        egraph: EGraph<L, N>,
        eq_rules: implvec!(Rewrite<L, N>),
        rules: implvec!(Box<dyn Rule<L, N>>),
    ) -> Self {
        Self {
            egraph: Some(egraph),
            eq_rules: eq_rules.into_iter().collect(),
            rules: rules.into_iter().map_into().collect(),
            memo: Default::default(),
            clean: true,
            runner_config: Default::default(),
        }
    }

    pub fn run_expr(&mut self, goal: RecExpr<L>) -> bool {
        let goal = self.egraph.as_mut().unwrap().add_expr(&goal);
        self.run_egraph();
        self.run(goal)
    }

    pub fn run(&mut self, goal: egg::Id) -> bool {
        if true || cfg!(debug_assertions) {
            let g = self.egraph().id_to_expr(goal);
            println!("{}", g.pretty(80))
        }
        use std::collections::hash_map::Entry;
        let memo = match self.memo.entry(goal) {
            Entry::Occupied(occupied_entry) => {
                let res = occupied_entry.get().borrow().as_bool();
                if true || cfg!(debug_assertions) {
                    println!("skipping: {:}", res)
                }
                return res;
            }
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(Rc::new(RefCell::new(Status::InProgress)))
            }
        }
        .clone();
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
                .any(|goals| goals.iter().all(|g| self.run(*g)));
            if ret || search.cut() {
                break ret; // found a proof or cut
            }
        };
        *memo.borrow_mut() = ret.into();
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
            eprintln!("--------------run egraph-------------");
            let runner = self
                .runner_config
                .apply(Runner::<L, N>::new(Default::default()))
                .with_egraph(egraph)
                .run(&self.eq_rules);
            dbg!(&runner.stop_reason);

            if !matches!(
                &runner.stop_reason,
                Some(StopReason::Saturated) | Some(StopReason::IterationLimit(_))
            ) {
                // runner.egraph.dot().to_pdf("/tmp/out.pdf");
                panic!("unclean graph: {:?}", runner.stop_reason)
            }

            egraph = runner.egraph;
            // self.memo.canonicalise(&egraph);
            {
                let memo = std::mem::take(&mut self.memo);
                self.memo = memo
                    .into_iter()
                    .map(|(id, s)| (egraph.find(id), s))
                    .collect();
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
            runner_config: Default::default(),
        })
    }
}
