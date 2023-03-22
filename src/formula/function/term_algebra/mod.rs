use self::{
    base_function::BaseFunction, cell::Cell, connective::Connective, quantifier::Quantifier,
};

pub mod base_function;
pub mod cell;
pub mod connective;
pub mod quantifier;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TermAlgebra<'bump> {
    Condition(Connective),
    Quantifier(Quantifier<'bump>),
    Function(BaseFunction<'bump>),
    Cell(Cell<'bump>),
    Input,
    IfThenElse,
}
