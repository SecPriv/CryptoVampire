use std::any::Any;
use std::borrow::Cow;
use std::fmt::Display;
use std::rc::Rc;
use std::str::FromStr;
use std::sync::atomic::{AtomicU64, Ordering};

use bon::{bon, builder};
use egg::{FromOp, Id, Language, Pattern, RecExpr, Searcher, SymbolLang};
use serde::Serialize;
use thiserror::Error;
use utils::{ereturn_if, ereturn_let};

use super::{Dependancy, Fresh, Rule};
use crate::Program;
use crate::analysis::WeightedAnalysis;
use crate::proof::Payload;
use crate::rule::dynamic::DRule;
use crate::rule::prolog::prolog_builder::{SetRcPayload, State};
use crate::weight::Weight;

/// Represents a Prolog-like rule for the e-graph.
#[derive(Debug)]
pub struct PrologRule<L> {
    /// The input pattern of the rule.
    pub input: Pattern<L>,
    /// The dependencies of the rule.
    pub deps: Vec<Pattern<L>>,
    /// Whether the rule is a cut rule.
    pub cut: bool,
    /// Whether the rule requires a decrease in weight.
    pub require_decrease: bool,
    // pub free_vars: Vec<Var>,
    /// The name of the rule.
    pub name: Option<String>,
    // pub memo: RefCell<HashMap<Id, Dependancy>>,
    pub payload: Option<Payload>,
}

/// Errors that can occur during the construction of a `PrologRule`.
#[derive(Debug, Clone, Copy, Error)]
#[non_exhaustive]
pub enum PrologBuilderError {
    /// Occurs when a premise refers to a free variable that is not bound by the input pattern.
    #[error("premise refer to free variable {0}")]
    VariableMishmatch(egg::Var),
}

#[bon]
impl<L: Language> PrologRule<L> {
    /// Creates a new `PrologRule`.
    #[builder(builder_type = PrologBuilder)]
    pub fn new(
        input: Pattern<L>,
        #[builder(with = <_>::from_iter, default = vec![])] deps: Vec<Pattern<L>>,
        #[builder(default = false)] cut: bool,
        #[builder(default = false)] require_decrease: bool,
        #[builder(into)] name: Option<String>,
        rc_payload: Option<Payload>,
    ) -> Result<Self, PrologBuilderError> {
        let bound_vars = input.vars();
        for v in deps.iter().flat_map(|d| d.vars().into_iter()) {
            if !bound_vars.contains(&v) {
                return Err(PrologBuilderError::VariableMishmatch(v));
            }
        }

        Ok(Self {
            input,
            deps,
            cut,
            require_decrease,
            name,
            payload: rc_payload,
        })
    }
}

impl<S, L> PrologBuilder<L, S>
where
    L: Language,
    S: State,
{
    pub fn payload<T: Sized + Sync + Send + 'static>(
        self,
        x: T,
    ) -> PrologBuilder<L, SetRcPayload<S>>
    where
        S::RcPayload: crate::rule::prolog::prolog_builder::IsUnset,
    {
        self.rc_payload(Box::<dyn Any + Send + Sync>::from(Box::new(x)).into())
    }
}

impl<L> FromStr for PrologRule<L>
where
    anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
    L: FromOp,
{
    /// The error type returned when parsing fails.
    type Err = anyhow::Error;

    /// Parses a string into a `PrologRule`.
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name, s) = parser::extract_name(s)?;
        parser::parse_pl(name, s)
    }
}

static NUM_VARS: AtomicU64 = AtomicU64::new(u64::MAX / 8);

impl Fresh for SymbolLang {
    /// Creates a fresh `RecExpr<SymbolLang>`.
    fn mk_fresh() -> RecExpr<Self> {
        let s = format!("_fresh#{:}", NUM_VARS.fetch_add(1, Ordering::AcqRel));
        dbg!(&s);
        SymbolLang::leaf(s).build_recexpr(|_| unreachable!())
    }
}

impl<L, N, R> Rule<L, N, R> for PrologRule<L>
where
    L: Language + Display + Serialize,
    N: WeightedAnalysis<L> + Serialize,
    N::Data: Serialize,
{
    /// Searches for matches of the rule in the e-graph and returns the dependencies.
    fn search(&self, prgm: &mut Program<L, N, R>, goal: Id) -> Dependancy {
        let matches = self.input.search_eclass(prgm.egraph(), goal);
        ereturn_let!(let Some(matches) = matches, Dependancy::impossible());

        let weight = N::get_weight(&prgm.egraph()[goal].data);
        let inner: Vec<Vec<Id>> = matches
            .substs
            .into_iter()
            .filter_map(|subst| {
                let deps: Vec<Id> = self
                    .deps
                    .iter()
                    .map(|ret| ret.apply_susbt(prgm.egraph_mut(), &subst))
                    .collect();
                let does_decrease = !self.require_decrease
                    || deps
                        .iter()
                        .all(|id| N::get_weight(&prgm.egraph()[*id].data).decreases(&weight));

                does_decrease.then_some(deps)
            })
            .collect();
        prgm.config.node_limit += inner.iter().map(|x| x.len()).sum::<usize>();

        Dependancy {
            inner,
            cut: self.cut,
            payload: self.payload.clone(),
        }
    }

    /// Debugs the rule.
    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<prolog> ")?;
        if let Some(name) = &self.name {
            write!(f, "[{name}] ")?;
        }

        write!(f, "{}", self.input)?;

        if self.deps.is_empty() && !self.cut && !self.require_decrease {
            return write!(f, ".");
        }

        write!(f, " :- ")?;
        if self.cut {
            write!(f, "!, ")?;
        }
        if self.require_decrease {
            write!(f, "@, ")?;
        }
        for dep in &self.deps {
            write!(f, "{dep}, ")?;
        }

        write!(f, "true.")
    }

    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        if let Some(name) = &self.name {
            format!("prolog({name})").into()
        } else {
            Cow::Borrowed("prolog")
        }
    }
}

impl<L, N> From<PrologRule<L>> for DRule<L, N>
where
    L: Language + Display + Serialize + 'static,
    N: Default + WeightedAnalysis<L> + Serialize,
    N::Data: Serialize,
{
    /// Converts a `PrologRule` into an `Rc<dyn Rule<L, N>>`.
    fn from(val: PrologRule<L>) -> Self {
        DRule::new(val)
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

pub mod parser {

    use std::fmt::Debug;
    use std::str::FromStr;

    use anyhow::{Context, anyhow, bail};
    use egg::{Analysis, FromOp, Language, MultiPattern, Pattern, Rewrite};
    use log::trace;

    use super::PrologRule;

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
                require_decrease: false,
                // free_vars: vec![],
                name,
                // memo: RefCell::new(Default::default()),
                payload: None,
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
                let no_free_vars = deps
                    .iter()
                    .flat_map(|p| p.vars().into_iter())
                    .all(|v| bound_vars.contains(&v));
                anyhow::ensure!(no_free_vars, "there are free variables! ({:?})", name);

                let result = PrologRule {
                    input: head,
                    deps,
                    cut,
                    // free_vars,
                    require_decrease: decrease,
                    name,
                    payload: None, // memo: RefCell::new(Default::default()),
                };

                trace!("parsed {result:?}");

                Ok(result)
            }
        }
    }

    /// Represents either a `PrologRule` or a `Rewrite`.
    pub enum PlOrRw<L, N> {
        Pl(PrologRule<L>),
        Rw(Rewrite<L, N>),
    }

    impl<L, N> Debug for PlOrRw<L, N>
    where
        Rewrite<L, N>: Debug,
        PrologRule<L>: Debug,
    {
        /// Formats the `PlOrRw` for debugging.
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            match self {
                Self::Pl(arg0) => f.debug_tuple("Pl").field(arg0).finish(),
                Self::Rw(arg0) => f.debug_tuple("Rw").field(arg0).finish(),
            }
        }
    }

    impl<L, N> From<PrologRule<L>> for PlOrRw<L, N> {
        /// Converts a `PrologRule` into a `PlOrRw`.
        fn from(v: PrologRule<L>) -> Self {
            Self::Pl(v)
        }
    }

    impl<L, N> From<Rewrite<L, N>> for PlOrRw<L, N> {
        /// Converts a `Rewrite` into a `PlOrRw`.
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

    /// Extracts the name from a rule string.
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
        let cleaned = s
            .lines()
            .map(|line| {
                let line = line.trim();
                // Remove anything after a '%'
                match line.find('%') {
                    Some(idx) => &line[..idx],
                    None => line,
                }
                .trim()
            })
            .filter(|line| !line.is_empty())
            .collect::<Vec<_>>()
            .join(" ");

        cleaned
            .trim_end()
            .split('.')
            .filter(|part| !part.trim().is_empty())
            .map(parse_one)
            .collect()
    }

    impl<L, N> FromStr for PlOrRw<L, N>
    where
        L: Language + Sync + Send + FromOp + 'static,
        N: Analysis<L>,
        anyhow::Error: From<<Pattern<L> as FromStr>::Err>,
        anyhow::Error: From<<MultiPattern<L> as FromStr>::Err>,
    {
        /// The error type returned when parsing fails.
        type Err = anyhow::Error;

        /// Parses a string into a `PlOrRw`.
        fn from_str(s: &str) -> Result<Self, Self::Err> {
            parse_one(s)
        }
    }

    impl<L, N> PlOrRw<L, N> {
        /// Parses a program string into a vector of `PlOrRw`.
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
