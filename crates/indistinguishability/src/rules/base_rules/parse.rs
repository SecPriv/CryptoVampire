//! quick parser for [PatternAst] and [egg::MutlipatternAst]
use std::{error::Error, str::FromStr};

use egg::{Analysis, Language, MultiPattern, Pattern, PatternAst, Rewrite, SymbolLang, Var};
use itertools::Itertools;
use logic_formula::egg::{SimplLang, SimpleDiscriminant, SimpleLangParseError};
use utils::{impossible::Impossible, iter_array::IntoArray};

/// Only use for quick 'n dirty parsing: no error handling
#[derive(Debug)]
pub(crate) enum Patterns<L> {
    Pattern {
        name: String,
        from: PatternAst<L>,
        to: PatternAst<L>,
    },
    MultiPattern {
        name: String,
        from: Vec<(Var, PatternAst<L>)>,
        to: Vec<(Var, PatternAst<L>)>,
    },
}

impl Patterns<SymbolLang> {
    pub fn convert<const N: usize, D, E>(
        self,
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<Patterns<SimplLang<D, N>>, SimpleLangParseError<E>>
    where
        D: SimpleDiscriminant,
        E: Error,
    {
        match self {
            Patterns::Pattern { name, from, to } => Ok(Patterns::Pattern {
                name,
                from: SimplLang::from_var_symbollang(&from, &mut convert)?,
                to: SimplLang::from_var_symbollang(&to, &mut convert)?,
            }),
            Patterns::MultiPattern { name, from, to } => {
                let from = from
                    .into_iter()
                    .map(|(v, patt)| {
                        SimplLang::from_var_symbollang(&patt, &mut convert).map(|x| (v, x))
                    })
                    .try_collect()?;
                let to = to
                    .into_iter()
                    .map(|(v, patt)| {
                        SimplLang::from_var_symbollang(&patt, &mut convert).map(|x| (v, x))
                    })
                    .try_collect()?;
                Ok(Patterns::MultiPattern { name, from, to })
            }
        }
    }
}

impl<L: Language + Sync + Send + 'static> Patterns<L> {
    pub fn to_rewrite<N: Analysis<L>>(self) -> Result<Rewrite<L, N>, String> {
        match self {
            Patterns::Pattern { name, from, to } => {
                Rewrite::new(name, Pattern::new(from), Pattern::new(to))
            }
            Patterns::MultiPattern { name, from, to } => {
                Rewrite::new(name, MultiPattern::new(from), MultiPattern::new(to))
            }
        }
    }
}

impl FromStr for Patterns<SymbolLang> {
    type Err = Impossible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name, rest) = extract_name(s);
        let (from, to) = rest
            .split("=>")
            .collect_tuple()
            .expect("wrong number of `=>` (expected exactly one)");
        let (from, to) = (from.trim(), to.trim());
        let name = name.to_owned();
        if from.contains('=') {
            debug_assert!(to.contains('='));
            let from = parse_mpatt(from);
            let to = parse_mpatt(to);
            Ok(Patterns::MultiPattern { name, from, to })
        } else {
            debug_assert!(!to.contains('='));
            let from = parse_patt(from);
            let to = parse_patt(to);
            Ok(Patterns::Pattern { name, from, to })
        }
    }
}

fn extract_name(init_s: &str) -> (&str, &str) {
    let s = init_s.trim();

    if let Some(rest) = s.strip_prefix('[') {
        if let Some(end_bracket) = rest.find(']') {
            let name = &rest[..end_bracket];
            let after = &rest[end_bracket + 1..];
            (name, after)
        } else {
            panic!("no closing bracket in {s}");
        }
    } else {
        panic!("need name in {s}")
    }
}

fn parse_mpatt(s: &str) -> Vec<(Var, PatternAst<SymbolLang>)> {
    s.split(',')
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .flat_map(|s| {
            let mut splits = s.split('=');
            let var: Var = splits
                .next()
                .expect("no enough `=`")
                .parse()
                .expect("unable to parse variable");
            let assgn = splits.map(|s| s.trim().parse().expect("unable to parse mw"));
            assgn.map(move |a| (var, a))
        })
        .collect()
}

fn parse_patt(s: &str) -> PatternAst<SymbolLang> {
    s.trim().parse().expect("couldn't parse pattern")
}
