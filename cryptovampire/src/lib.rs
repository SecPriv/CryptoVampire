#![allow(dead_code)]

use cryptovampire_lib::{
    container::ScopedContainer,
    formula::{function::Function, sort::Sort},
    problem::Problem,
};
use utils::{implvec, traits::NicerError};
pub mod cli;
pub mod parser;

pub fn problem_try_from_str<'a, 'bump>(
    container: &'bump ScopedContainer<'bump>,
    sort_hash: implvec!(Sort<'bump>),
    function_hash: implvec!(Function<'bump>),
    extra_names: implvec!(String),
    str: &'a str,
    ignore_lemmas: bool
) -> anyhow::Result<Problem<'bump>> {
    parser::parse_str(container, sort_hash, function_hash, extra_names, str, ignore_lemmas)
}
