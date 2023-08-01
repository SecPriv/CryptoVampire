use crate::{assert_variance, variants, CustomDerive};

use self::{
    base_function::BaseFunction, cell::Cell, connective::Connective, if_then_else::IfThenElse,
    input::Input, name::Name, quantifier::Quantifier,
};

pub mod base_function;
pub mod cell;
pub mod connective;
pub mod if_then_else;
pub mod input;
pub mod name;
pub mod quantifier;

use macro_attr::*;

macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone,
        CustomDerive!(maybe_evaluate, 'bump),
        CustomDerive!(maybe_fixed_signature, 'bump),
    )]
    pub enum TermAlgebra<'bump> {
        Condition(Connective),
        Quantifier(Quantifier<'bump>),
        Function(BaseFunction<'bump>),
        Cell(Cell<'bump>),
        Name(Name<'bump>),
        Input(Input),
        IfThenElse(IfThenElse),
    }
}

impl<'bump> TermAlgebra<'bump> {
    pub fn is_default_subterm(&self) -> bool {
        match self {
            TermAlgebra::Condition(_)
            | TermAlgebra::Function(_)
            | TermAlgebra::IfThenElse(_)
            | TermAlgebra::Name(_) => true,
            TermAlgebra::Quantifier(_) | TermAlgebra::Cell(_) | TermAlgebra::Input(_) => false,
        }
    }

    variants!(TermAlgebra;
        Condition:Connective,
        Quantifier:Quantifier<'bump>,
        Function:BaseFunction<'bump>,
        Cell:Cell<'bump>,
        Name:Name<'bump>);
}

assert_variance!(TermAlgebra);
