use super::{function::Function, quantifier::Quantifier, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Formula {
    Var(Variable),
    Fun(Function, Vec<Formula>),
    Quantifier(Quantifier, Vec<Formula>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable {
    id: usize,
    sort: Sort,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CNF(Vec<Vec<Formula>>);
