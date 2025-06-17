//! quick parser for [PatternAst] and [egg::MutlipatternAst]
use std::{error::Error, str::FromStr};

use egg::{Analysis, Language, MultiPattern, Pattern, PatternAst, Rewrite, SymbolLang, Var};
use golgge::PrologRule;
use itertools::Itertools;
use logic_formula::egg::{SimplLang, SimpleDiscriminant, SimpleLangParseError};
use utils::impossible::Impossible;

use crate::{Lang, Problem, terms::Function};

/// remove comments from input
pub fn clean_input(s: &str) -> String {
    s.lines()
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
        .join(" ")
}

/// Only use for quick 'n dirty parsing: no error handling
#[derive(Debug)]
pub(crate) enum PatternsAst<L> {
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

/// Only use for quick 'n dirty parsing: no error handling
#[derive(Debug)]
pub(crate) struct PrologAst<L> {
    pub input: PatternAst<L>,
    pub deps: Vec<PatternAst<L>>,
    pub cut: bool,
    pub require_decrease: bool,
    pub name: Option<String>,
}

impl PatternsAst<SymbolLang> {
    pub fn convert<const N: usize, D, E>(
        self,
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<PatternsAst<SimplLang<D, N>>, SimpleLangParseError<E>>
    where
        D: SimpleDiscriminant,
        E: Error,
    {
        match self {
            PatternsAst::Pattern { name, from, to } => Ok(PatternsAst::Pattern {
                name,
                from: SimplLang::from_var_symbollang(&from, &mut convert)?,
                to: SimplLang::from_var_symbollang(&to, &mut convert)?,
            }),
            PatternsAst::MultiPattern { name, from, to } => {
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
                Ok(PatternsAst::MultiPattern { name, from, to })
            }
        }
    }
}

impl<L: Language + Sync + Send + 'static> PatternsAst<L> {
    pub fn into_rewrite<N: Analysis<L>>(self) -> Result<Rewrite<L, N>, String> {
        match self {
            PatternsAst::Pattern { name, from, to } => {
                Rewrite::new(name, Pattern::new(from), Pattern::new(to))
            }
            PatternsAst::MultiPattern { name, from, to } => {
                Rewrite::new(name, MultiPattern::new(from), MultiPattern::new(to))
            }
        }
    }
}

impl FromStr for PatternsAst<SymbolLang> {
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
            Ok(PatternsAst::MultiPattern { name, from, to })
        } else {
            debug_assert!(!to.contains('='));
            let from = parse_patt(from);
            let to = parse_patt(to);
            Ok(PatternsAst::Pattern { name, from, to })
        }
    }
}

impl PrologAst<SymbolLang> {
    pub fn convert<const N: usize, D, E>(
        self,
        mut convert: impl FnMut(&str) -> Result<D, E>,
    ) -> Result<PrologAst<SimplLang<D, N>>, SimpleLangParseError<E>>
    where
        D: SimpleDiscriminant,
        E: Error,
    {
        let Self {
            input,
            deps,
            cut,
            require_decrease,
            name,
        } = self;
        let input = SimplLang::from_var_symbollang(&input, &mut convert)?;
        let deps = deps
            .iter()
            .map(|r| SimplLang::from_var_symbollang(r, &mut convert))
            .collect::<Result<_, _>>()?;
        Ok(PrologAst {
            input,
            deps,
            cut,
            require_decrease,
            name,
        })
    }
}

impl<L: Language> PrologAst<L> {
    pub fn into_prolog(self) -> PrologRule<L> {
        let Self {
            input,
            deps,
            cut,
            require_decrease,
            name,
        } = self;
        PrologRule {
            input: Pattern::new(input),
            deps: deps.into_iter().map(Pattern::new).collect(),
            cut,
            require_decrease,
            name,
        }
    }
}

impl FromStr for PrologAst<SymbolLang> {
    type Err = Impossible;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (name, rest) = extract_name(s);
        let (input, deps) = rest
            .split(":-")
            .collect_tuple()
            .expect("need exactly one `:-`");

        let mut require_decrease = false;
        let mut cut = false;

        let input = parse_patt(input);
        let deps = deps
            .split(',')
            .filter(|x| !x.is_empty())
            .map(str::trim)
            .filter(|x| {
                cut |= *x == "!";
                require_decrease |= *x == "@";
                *x != "@" && *x != "!"
            })
            .map(parse_patt)
            .collect();

        Ok(Self {
            input,
            deps,
            cut,
            require_decrease,
            name: Some(name.into()),
        })
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

pub(crate) fn convert_fun(pbl: &Problem, s: &str) -> Result<Function, Impossible> {
    // Ok(pbl.function.get(s).expect()
    match pbl.function.get(s) {
        Some(s) => Ok(s),
        _ => panic!("unknown function {s}"),
    }
}
