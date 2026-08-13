use crate::terms::{Function, INIT, Variable};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Constrains {
    pub op: ConstrainOp,
    pub arg1: BoundStep,
    pub arg2: BoundStep,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ConstrainOp {
    LessThan,
    Exclude,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoundStep {
    pub head: Function,
    pub args: Vec<Variable>,
}

impl BoundStep {
    pub fn init() -> Self {
        Self {
            head: INIT.clone(),
            args: vec![],
        }
    }
}
