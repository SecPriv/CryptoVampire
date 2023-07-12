use crate::assert_variance;

use self::{
    base_function::BaseFunction, cell::Cell, connective::Connective, name::Name,
    quantifier::Quantifier,
};

pub mod base_function;
pub mod cell;
pub mod connective;
pub mod name;
pub mod quantifier;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum TermAlgebra<'bump> {
    Condition(Connective),
    Quantifier(Quantifier<'bump>),
    Function(BaseFunction<'bump>),
    Cell(Cell<'bump>),
    Name(Name<'bump>),
    Input,
    IfThenElse,
}

impl<'bump> TermAlgebra<'bump> {
    pub fn is_default_subterm(&self) -> bool {
        match self {
            TermAlgebra::Condition(_)
            | TermAlgebra::Function(_)
            | TermAlgebra::IfThenElse
            | TermAlgebra::Name(_) => true,
            TermAlgebra::Quantifier(_) | TermAlgebra::Cell(_) | TermAlgebra::Input => false,
        }
    }
}

assert_variance!(TermAlgebra);
