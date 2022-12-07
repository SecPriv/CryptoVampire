use crate::formula::{
    formula::{Formula, CNF},
    sort::Sort,
};

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct Protocol {
    steps: Vec<Step>,
}

impl Protocol {
    pub fn new(steps: Vec<Step>) -> Self {
        Self { steps }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Step {
    parameters: Vec<Sort>,
    condition: CNF,
    message: Formula,
}

impl Step {
    pub fn new(parameters: Vec<Sort>, condition: CNF, message: Formula) -> Self {
        Self {
            parameters,
            condition,
            message,
        }
    }
}
