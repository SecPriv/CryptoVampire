use crate::Program;
use egg::{Analysis, FromOp, Id, Language, Pattern, RecExpr, Searcher, SymbolLang, Var};
use std::{
    str::FromStr,
    sync::atomic::{AtomicU64, Ordering},
    u64,
};

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash, Clone)]
pub struct Dependancy {
    inner: Vec<Vec<Id>>,
    cut: bool,
}

impl Default for Dependancy {
    fn default() -> Self {
        Self {
            inner: vec![],
            cut: false,
        }
    }
}

impl Dependancy {
    pub fn new(inner: Vec<Vec<Id>>) -> Self {
        Self { inner, cut: false }
    }

    pub fn inner(&self) -> &Vec<Vec<Id>> {
        &self.inner
    }

    pub fn cut(&self) -> bool {
        self.cut
    }

    pub fn set_cut(self, cut: bool) -> Self {
        Self { cut, ..self }
    }

    pub fn do_cut(self) -> Self {
        self.set_cut(true)
    }

    pub fn do_not_cut(self) -> Self {
        self.set_cut(false)
    }
}

pub trait Rule<L: Language, N: Analysis<L>> {
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy;
}

pub trait Fresh : Sized {
    fn mk_fresh() -> RecExpr<Self>;
}

impl<L: Language, N: Analysis<L> + Default, F> Rule<L, N> for F
where
    F: Fn(&mut Program<L, N>, Id) -> Dependancy,
{
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy {
        self(prgm, goal)
    }
}

#[derive(Debug)]
pub struct PrologRule<L> {
    pub input: Pattern<L>,
    pub deps: Vec<Pattern<L>>,
    pub cut: bool,
    pub free_vars: Vec<Var>,
}

impl<L> FromStr for PrologRule<L>
where
    anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    L: FromOp,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parser::parse_pl(s)
    }
}

static NUM_VARS: AtomicU64 = AtomicU64::new(u64::MAX / 8);

impl Fresh for SymbolLang {
    fn mk_fresh() -> RecExpr<Self> {
        let s= format!(
            "_fresh#{:}",
            NUM_VARS.fetch_add(1, Ordering::AcqRel)
        );
        dbg!(&s);
        SymbolLang::leaf(s).build_recexpr(|_| unreachable!())
    }
}

impl<L: Language + Fresh, N: Analysis<L> + Default> Rule<L, N> for PrologRule<L> {
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy {
        let matches = self.input.search_eclass(prgm.egraph(), goal);
        let Some(matches) = matches else {
            return Default::default();
        };
        // let subst = matches.substs.first().unwrap();
        let inner = matches
            .substs
            .into_iter()
            .map(|mut subst| {
                for v in &self.free_vars {
                    let id = prgm.egraph_mut().add_expr(&Fresh::mk_fresh());
                    subst.insert(*v, id);
                }
                self.deps
                    .iter()
                    .map(|ret| ret.apply_susbt(prgm.egraph_mut(), &subst))
                    .collect()
            })
            .collect();
        Dependancy {
            inner,
            cut: self.cut,
        }
    }
}

#[macro_export]
macro_rules! pl {
    // ($a:literal) => {$a.parse().unwrap()};
    ($a:literal :- $($c:literal),*) => {
        $crate::PrologRule {
            input: $a.parse().unwrap(),
            dep: vec![$($c.parse().unwrap()),*],
            cut: false
        }
    };
    ($a:literal :-! $($c:literal),*.?) => {
        $crate::PrologRule {
            input: $a.parse().unwrap(),
            dep: vec![$($c.parse().unwrap()),*],
            cut: true
        }
    };
}

mod parser {
    use super::PrologRule;
    use anyhow::{anyhow, bail, Context};
    use egg::{Analysis, FromOp, Language, MultiPattern, Pattern, Rewrite, SymbolLang};
    use itertools::Itertools;
    use std::{fmt::Debug, str::FromStr};

    fn parse_rw<L, N>(s1: &str, s2: &str) -> anyhow::Result<Rewrite<L, N>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    {
        dbg!(s1);
        dbg!(s2);
        let searcher: Pattern<L> = s1.parse()?;
        let applier: Pattern<L> = s2.parse()?;
        Rewrite::new("", searcher, applier).map_err(|e| anyhow!("{e}"))
    }

    fn parse_multirw<L, N>(s1: &str, s2: &str) -> anyhow::Result<Rewrite<L, N>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        dbg!(s1);
        dbg!(s2);
        let searcher: MultiPattern<L> = s1.parse()?;
        let applier: MultiPattern<L> = s2.parse()?;
        Rewrite::new("", searcher, applier).map_err(|e| anyhow!("{e}"))
    }

    pub fn parse_pl<L: FromOp>(s: &str) -> anyhow::Result<PrologRule<L>>
    where
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    {
        dbg!(s);
        let mut s = s.split(":-");
        let head: Pattern<L> = s.next().with_context(|| "empty string")?.parse()?;
        match s.next() {
            None => Ok(PrologRule {
                input: head,
                deps: vec![],
                cut: false,
                free_vars: vec![],
            }),
            Some(ns) => {
                let ns = ns.trim();
                if s.next().is_some() {
                    bail!("two ':-; ??")
                };
                let cut = ns.starts_with('!');
                let s = if cut { &ns[1..] } else { ns };
                let deps: Result<Vec<Pattern<L>>, _> = s.split(',').filter(|x| !x.is_empty()).map(|x| x.parse()).collect();
                let deps = deps?;
                let bound_vars = head.vars();
                let free_vars = deps
                    .iter()
                    .flat_map(|p| p.vars().into_iter())
                    .unique()
                    .filter(|v| !bound_vars.contains(v))
                    .collect();
                dbg!(&free_vars);
                Ok(PrologRule {
                    input: head,
                    deps,
                    cut,
                    free_vars,
                })
            }
        }
    }

    pub enum PlOrRw<L, N> {
        Pl(PrologRule<L>),
        Rw(Rewrite<L, N>),
    }

    impl<L, N> Debug for PlOrRw<L, N>
    where
        Rewrite<L, N>: Debug,
        PrologRule<L>: Debug,
    {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pl(arg0) => f.debug_tuple("Pl").field(arg0).finish(),
                Self::Rw(arg0) => f.debug_tuple("Rw").field(arg0).finish(),
            }
        }
    }

    impl<L, N> From<PrologRule<L>> for PlOrRw<L, N> {
        fn from(v: PrologRule<L>) -> Self {
            Self::Pl(v)
        }
    }

    impl<L, N> From<Rewrite<L, N>> for PlOrRw<L, N> {
        fn from(v: Rewrite<L, N>) -> Self {
            Self::Rw(v)
        }
    }

    fn parse_one<L, N>(s: &str) -> anyhow::Result<PlOrRw<L, N>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        if s.contains("=>") {
            let mut iter = s.split("=>");
            let s1 = iter.next().context("x")?;
            let s2 = iter.next().context("x")?;
            if iter.next().is_some() {
                bail!("too many =>")
            }
            if s1.contains('=') {
                Ok(parse_multirw(s1, s2)?.into())
            } else {
                Ok(parse_rw(s1, s2)?.into())
            }
        } else {
            Ok(parse_pl(s)?.into())
        }
    }

    fn parse<L, N>(s: &str) -> anyhow::Result<Vec<PlOrRw<L, N>>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        s.trim_end()
            .split('.')
            .filter(|part| !part.is_empty())
            .map(parse_one)
            .collect()
    }

    #[test]
    fn test() {
        let s = include_str!("../tests/test.pl");
        let r: Vec<PlOrRw<SymbolLang, ()>> = parse(s).unwrap();
        println!("{r:?}")
    }

    impl<L, N> FromStr for PlOrRw<L, N>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        type Err = anyhow::Error;

        fn from_str(s: &str) -> Result<Self, Self::Err> {
            parse_one(s)
        }
    }

    impl<L, N> PlOrRw<L, N> {
        pub fn parse_program(s: &str) -> anyhow::Result<Vec<Self>>
        where
            L: Language + Sync + Send + FromOp + 'static,
            N: Analysis<L>,
            anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
            anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
        {
            parse(s)
        }
    }
}
pub use parser::PlOrRw;
