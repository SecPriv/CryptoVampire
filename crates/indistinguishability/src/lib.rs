use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Rewrite, Runner,
};
use itertools::{Either, Itertools};
use rule::PlOrRw;
use std::{
    cell::RefCell,
    collections::{hash_map::Entry, HashMap},
    rc::Rc,
    str::FromStr,
};
use utils::implvec;

mod rule;
pub use rule::{Dependancy, PrologRule, Rule};
// mod language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Status {
    True,
    False,
    InProgress,
}

pub struct Program<L: Language, N: Analysis<L>> {
    egraph: Option<EGraph<L, N>>,
    eq_rules: Vec<Rewrite<L, N>>,
    rules: Vec<Rc<dyn Rule<L, N>>>,
    memo: HashMap<Id, Status>,
    clean: bool,
}

impl<L: Language, N: Analysis<L> + Default> Program<L, N> {
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
        }
    }

    pub fn run_expr(&mut self, goal: RecExpr<L>) -> bool {
        let goal = self.egraph.as_mut().unwrap().add_expr(&goal);
        self.run_egraph();
        self.run(goal)
    }

    pub fn run(&mut self, goal: egg::Id) -> bool {
        if cfg!(debug_assertions) {
            let g = self.egraph().id_to_expr(goal);
            dbg!(g);
        }
        match self.memo.entry(goal) {
            Entry::Occupied(occupied_entry) => return occupied_entry.get().as_bool(),
            Entry::Vacant(vacant_entry) => {
                vacant_entry.insert(Status::InProgress);
            }
        }
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
        self.memo.insert(goal, ret.into());
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
            egraph = Runner::<L, N>::new(Default::default())
                .with_egraph(egraph)
                .run(&self.eq_rules)
                .egraph;
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
    L: Language + Sync + Send + FromOp + 'static,
    N: Analysis<L> + Default,
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
        })
    }
}
