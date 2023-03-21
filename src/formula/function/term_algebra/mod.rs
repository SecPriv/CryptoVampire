use self::{connective::Connective, quantifier::Quantifier, base_function::BaseFunction, cell::Cell};

pub mod base_function;
pub mod connective;
pub mod quantifier;
pub mod cell;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TermAlgebra<'bump> {
    Condition(Connective),
    Quantifier(Quantifier<'bump>),
    Function(BaseFunction<'bump>),
    Cell(Cell<'bump>),
    Input,
    IfThenElse
}
