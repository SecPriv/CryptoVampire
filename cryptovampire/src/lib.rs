#![allow(dead_code)]

use cryptovampire_lib::{
    container::ScopedContainer,
    formula::{function::Function, sort::Sort},
    problem::Problem,
};
use utils::{implvec, traits::NicerError};
pub mod cli;
pub mod parser;
pub mod runner;
pub mod smt;

pub fn problem_try_from_str<'a, 'bump>(
    container: &'bump ScopedContainer<'bump>,
    sort_hash: implvec!(Sort<'bump>),
    function_hash: implvec!(Function<'bump>),
    extra_names: implvec!(String),
    str: &'a str,
) -> Result<Problem<'bump>, parser::E> {
    parser::parse_str(container, sort_hash, function_hash, extra_names, str).debug_continue()
}
