use crate::terms::{Function, Variable};

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
