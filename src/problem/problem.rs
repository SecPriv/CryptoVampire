use std::collections::HashMap;

use crate::formula::{formula::Formula, function::Function, sort::Sort};

use super::protocol::Step;

#[derive(Debug)]
pub struct Problem {
    steps: HashMap<String, Step>,
    functions: HashMap<String, Function>,
    sorts: Vec<Sort>,
    assertions: Vec<Formula>,
    query: Vec<Formula>,
    order: Vec<Formula>,
}
