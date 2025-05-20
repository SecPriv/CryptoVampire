use egg::{Analysis, Rewrite, SymbolLang};
use itertools::Itertools;
use logic_formula::egg::SimplLang;
use std::collections::HashMap;
use utils::impossible::Impossible;

use crate::{
    terms::{Function, PARSING_PAIRS},
    Configuration,
};
use parse::Patterns;

mod parse;
#[cfg(test)]
mod test;

/// build the default rewrite rules
pub fn mk_golgge_rewrites<const N: usize, A>(
    _config: &Configuration,
) -> impl Iterator<Item = Rewrite<SimplLang<Function, N>, A>>
where
    A: Analysis<SimplLang<Function, N>>,
{
    let hash_map: HashMap<_, _> = PARSING_PAIRS.iter().cloned().collect();
    let convert = move |s: &str| Ok::<_, Impossible>(hash_map.get(s).unwrap().clone());

    let cleaned = include_str!("builtin_rewrites")
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
        .join(" ") // rebuild a string without comments
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
        .map(move |patt: Patterns<SymbolLang>| {
            patt.convert(&convert).unwrap().to_rewrite().unwrap()
        })
}
