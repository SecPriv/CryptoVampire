use eclassmap::{ECallMap, Entry};
use egg::{
    Analysis, EGraph, FromOp, Id, Language, MultiPattern, Pattern, RecExpr, Rewrite, Runner,
    StopReason,
};
use itertools::{Either, Itertools};
use rule::PlOrRw;
use std::{cell::RefCell, fmt::Display, rc::Rc, str::FromStr, usize};
use utils::implvec;

mod rule;
pub use rule::{Dependancy, Fresh, PrologRule, Rule};
// mod language;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Status {
    True,
    False,
    InProgress,
}

mod eclassmap {
    use egg::{Analysis, EGraph, Id, Language};
    use utils::implvec;

    #[derive(Debug, Clone)]
    pub struct ECallMap<V>(Vec<(Id, V)>);

    impl<V> Default for ECallMap<V> {
        fn default() -> Self {
            Self::new([])
        }
    }

    impl<V> ECallMap<V> {
        pub fn new(i: implvec!((Id, V))) -> Self {
            ECallMap(i.into_iter().collect())
        }

        pub fn get(&self, id: Id) -> Option<&V> {
            self.0
                .iter()
                .filter_map(|(x, v)| (x == &id).then_some(v))
                .next()
        }

        pub fn entry(&mut self, id: Id) -> Entry<'_, V> {
            let tmp = self
                .0
                .iter_mut()
                .filter_map(|(x, v)| (x == &id).then_some(v))
                // safety: `v` is a &mut
                .map(|v| unsafe { std::ptr::NonNull::new_unchecked(v as *mut _) })
                .next();
            match tmp {
                Some(mut value) => Entry::Occupied(OccupiedEntry {
                    id,
                    // `v` is actually our &mut from above, in this branch it is only aliased by `self`
                    value: unsafe { value.as_mut() },
                }),
                None => Entry::Vacant(VacantEntry { map: self, id }),
            }
        }

        fn unchecked_insert(&mut self, id: Id, value: V) -> &mut (Id, V) {
            self.0.push((id, value));
            self.0.last_mut().unwrap()
        }

        pub fn canonicalise<L: Language, N: Analysis<L>>(&mut self, egraph: &EGraph<L, N>) {
            for (id, _) in &mut self.0 {
                let nid = egraph.find(*id);
                *id = nid
            }
        }
    }

    pub struct VacantEntry<'a, V> {
        map: &'a mut ECallMap<V>,
        id: Id,
    }

    impl<'a, V> VacantEntry<'a, V> {
        pub fn insert(self, value: V) -> &'a mut V {
            let id = self.id;
            let (_, v) = self.map.unchecked_insert(id, value);
            v
        }
    }

    pub struct OccupiedEntry<'a, V> {
        id: Id,
        value: &'a mut V,
    }

    impl<'a, V> OccupiedEntry<'a, V> {
        pub fn get(self) -> &'a mut V {
            self.value
        }
    }

    pub enum Entry<'a, V> {
        Vacant(VacantEntry<'a, V>),
        Occupied(OccupiedEntry<'a, V>),
    }

    impl<'a, V> Entry<'a, V> {
        pub fn id(&self) -> Id {
            match self {
                Entry::Vacant(VacantEntry { id, .. })
                | Entry::Occupied(OccupiedEntry { id, .. }) => *id,
            }
        }

        pub fn or_insert_with_key(self, f: impl FnOnce(Id) -> V) -> &'a mut V {
            match self {
                Entry::Vacant(_) => {
                    let default = f(self.id());
                    self.insert_entry(default)
                }
                Entry::Occupied(occupied_entry) => occupied_entry,
            }
            .value
        }

        pub fn or_inster(self, default: V) -> &'a mut V {
            self.or_insert_with_key(|_| default)
        }

        pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, V> {
            match self {
                Self::Occupied(e) => {
                    *e.value = value;
                    e
                }
                Self::Vacant(e) => OccupiedEntry {
                    id: e.id,
                    value: e.insert(value),
                },
            }
        }
    }
}

pub struct Program<L: Language, N: Analysis<L>> {
    egraph: Option<EGraph<L, N>>,
    eq_rules: Vec<Rewrite<L, N>>,
    rules: Vec<Rc<dyn Rule<L, N>>>,
    memo: ECallMap<Rc<RefCell<Status>>>,
    clean: bool,
    pub runner_config: RunnerConfig,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RunnerConfig {
    iter_limit: usize,
    node_limit: usize,
    time_limit: std::time::Duration,
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
        if cfg!(debug_assertions) {
            let g = self.egraph().id_to_expr(goal);
            println!("{}", g.pretty(80))
        }
        let memo = match self.memo.entry(goal) {
            Entry::Occupied(occupied_entry) => {
                let res = occupied_entry.get().borrow().as_bool();
                if cfg!(debug_assertions) {
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
                runner.egraph.dot().to_pdf("/tmp/out.pdf");
                panic!("unclean graph: {:?}", runner.stop_reason)
            }

            egraph = runner.egraph;
            self.memo.canonicalise(&egraph);
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
    L: Language + Sync + Send + FromOp + Fresh + Display + 'static,
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
            runner_config: Default::default(),
        })
    }
}
