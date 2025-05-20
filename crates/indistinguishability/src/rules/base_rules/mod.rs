use egg::{Analysis, Rewrite, SymbolLang};
use itertools::Itertools;
use logic_formula::egg::SimplLang;
use std::collections::HashMap;
use utils::impossible::Impossible;

use crate::{
    terms::{Function, PARSING_PAIRS},
    Configuration, Problem,
};
use parse::{clean_input, convert_fun, PatternsAst};

mod parse;
#[cfg(test)]
mod test;

/// build the default rewrite rules
pub fn mk_golgge_rewrites<const N: usize, A>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<SimplLang<Function, N>, A>> + use<'_, A, N>
where
    A: Analysis<SimplLang<Function, N>>,
{
    let cleaned = clean_input(include_str!("builtin_rewrites"))
        // rebuild a string without comments
        .split('.')
        .map(|x| x.trim().to_owned())
        .collect_vec(); // we need to collect here to force the iterator to take ownership

    cleaned
        .into_iter()
        .filter(|s| !s.is_empty())
        .inspect(|s| {
            dbg!(s);
        }) // uncomment to debug
        .map(|s| s.parse().unwrap())
        .map(move |patt: PatternsAst<SymbolLang>| {
            patt.convert(|s| convert_fun(pbl, s)).unwrap().into_rewrite().unwrap()
        })
}

pub use deduce::mk_deduce_rules;
mod deduce;
