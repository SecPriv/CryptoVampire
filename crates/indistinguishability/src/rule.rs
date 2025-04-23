use crate::{
    analysis::WeightedAnalysis,
    weight::{self, Weight},
    Program,
};
use egg::{Analysis, FromOp, Id, Language, Pattern, RecExpr, Searcher, SymbolLang, Var};
use std::{
    fmt::Display,
    str::FromStr,
    sync::atomic::{AtomicU64, Ordering},
    u64,
};

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash, Clone, Default)]
pub struct Dependancy {
    inner: Vec<Vec<Id>>,
    cut: bool,
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

pub trait Fresh: Sized {
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
    pub decrease: bool,
    pub free_vars: Vec<Var>,
    pub name: Option<String>,
}

impl<L> FromStr for PrologRule<L>
where
    anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    L: FromOp,
{
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name, s) = parser::extract_name(s)?;
        parser::parse_pl(name, s)
    }
}

static NUM_VARS: AtomicU64 = AtomicU64::new(u64::MAX / 8);

impl Fresh for SymbolLang {
    fn mk_fresh() -> RecExpr<Self> {
        let s = format!("_fresh#{:}", NUM_VARS.fetch_add(1, Ordering::AcqRel));
        dbg!(&s);
        SymbolLang::leaf(s).build_recexpr(|_| unreachable!())
    }
}

impl<L: Language + Fresh + Display, N: Default + WeightedAnalysis<L>> Rule<L, N> for PrologRule<L> {
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy {
        let matches = self.input.search_eclass(prgm.egraph(), goal);
        let Some(matches) = matches else {
            return Default::default();
        };
        let weight = N::get_weight(&prgm.egraph()[goal].data);
        // let subst = matches.substs.first().unwrap();
        let inner: Vec<Vec<Id>> = matches
            .substs
            .into_iter()
            .filter_map(|mut subst| {
                for v in &self.free_vars {
                    let id = prgm.egraph_mut().add_expr(&Fresh::mk_fresh());
                    subst.insert(*v, id);
                }
                let deps: Vec<Id> = self
                    .deps
                    .iter()
                    .map(|ret| ret.apply_susbt(prgm.egraph_mut(), &subst))
                    .collect();
                if self.decrease
                    && deps
                        .iter()
                        .any(|id| !N::get_weight(&prgm.egraph()[*id].data).decreases(&weight))
                {
                    None
                } else {
                    Some(deps)
                }
            })
            .collect();
        prgm.config.node_limit += inner.iter().map(|x| x.len()).sum::<usize>();
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

    fn parse_rw<L, N>(name: Option<&str>, s1: &str, s2: &str) -> anyhow::Result<Rewrite<L, N>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    {
        let searcher: Pattern<L> = s1.parse()?;
        let applier: Pattern<L> = s2.parse()?;
        let name = name.unwrap_or("");
        Rewrite::new(name, searcher, applier).map_err(|e| anyhow!("{e}"))
    }

    fn parse_multirw<L, N>(name: Option<&str>, s1: &str, s2: &str) -> anyhow::Result<Rewrite<L, N>>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        let searcher: MultiPattern<L> = s1.parse()?;
        let applier: MultiPattern<L> = s2.parse()?;
        let name = name.unwrap_or("");
        Rewrite::new(name, searcher, applier).map_err(|e| anyhow!("{e}"))
    }

    pub fn parse_pl<L: FromOp>(name: Option<&str>, s: &str) -> anyhow::Result<PrologRule<L>>
    where
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    {
        let mut s = s.split(":-");
        let head: Pattern<L> = s.next().with_context(|| "empty string")?.parse()?;
        let name = name.map(|s| s.to_owned());

        match s.next() {
            None => Ok(PrologRule {
                input: head,
                deps: vec![],
                cut: false,
                decrease: false,
                free_vars: vec![],
                name,
            }),
            Some(ns) => {
                let ns = ns.trim();
                if s.next().is_some() {
                    bail!("two ':-; ??")
                };
                let s = ns;

                let cut = s.starts_with('!');
                let s = if cut { s[1..].trim() } else { s };

                let decrease = s.starts_with('@');
                let s = if decrease { s[1..].trim() } else { s };

                let deps: Result<Vec<Pattern<L>>, _> = s
                    .split(',')
                    .filter(|x| !x.is_empty())
                    .map(|x| x.parse())
                    .collect();
                let deps = deps?;
                let bound_vars = head.vars();
                let free_vars: Vec<egg::Var> = deps
                    .iter()
                    .flat_map(|p| p.vars().into_iter())
                    .unique()
                    .filter(|v| !bound_vars.contains(v))
                    .collect();
                if !free_vars.is_empty() {
                    dbg!(&free_vars);
                }
                Ok(PrologRule {
                    input: head,
                    deps,
                    cut,
                    free_vars,
                    decrease,
                    name,
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
        let (name, s) = extract_name(s)?;

        if s.contains("=>") {
            let mut iter = s.split("=>");
            let s1 = iter.next().context("x")?;
            let s2 = iter.next().context("x")?;
            if iter.next().is_some() {
                bail!("too many =>")
            }
            if s1.contains('=') {
                Ok(parse_multirw(name, s1, s2)?.into())
            } else {
                Ok(parse_rw(name, s1, s2)?.into())
            }
        } else {
            Ok(parse_pl(name, s)?.into())
        }
    }

    pub(crate) fn extract_name(s: &str) -> anyhow::Result<(Option<&str>, &str)> {
        let s = s.trim();

        let (name, s) = if let Some(rest) = s.strip_prefix('[') {
            if let Some(end_bracket) = rest.find(']') {
                let name = &rest[..end_bracket];
                let after = &rest[end_bracket + 1..];
                (Some(name), after)
            } else {
                bail!("Unclosed braket")
            }
        } else {
            (None, s)
        };
        Ok((name, s))
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
        let s = include_str!("../tests/test");
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
