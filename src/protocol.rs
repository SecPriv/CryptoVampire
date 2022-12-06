use crate::formula::{MFormula, RcType, MCNF};

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
    parameters: Vec<RcType>,
    condition: MCNF,
    message: MFormula,
}

impl Step {
    pub fn new(parameters: Vec<RcType>, condition: MCNF, message: MFormula) -> Self {
        Self {
            parameters,
            condition,
            message,
        }
    }
}
