use std::collections::HashMap;

use crate::formula::{formula::RichFormula, function::Function, sort::Sort};

use super::protocol::Step;

#[derive(Debug)]
pub struct Problem {
    steps: HashMap<String, Step>,
    functions: HashMap<String, Function>,
    sorts: Vec<Sort>,
    assertions: Vec<RichFormula>,
    query: Vec<RichFormula>,
    order: Vec<RichFormula>,
    temporary: Vec<RichFormula>
}
