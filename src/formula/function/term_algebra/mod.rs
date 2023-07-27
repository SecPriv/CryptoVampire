use crate::{assert_variance, variants};

use self::{
    base_function::BaseFunction, cell::Cell, connective::Connective, name::Name,
    quantifier::Quantifier,
};

use super::Function;

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

    variants!(TermAlgebra;
        Condition:Connective,
        Quantifier:Quantifier<'bump>,
        Function:BaseFunction<'bump>,
        Cell:Cell<'bump>,
        Name:Name<'bump>);
}

assert_variance!(TermAlgebra);

pub trait Evaluatable<'bump> {
    fn get_evaluated(&self) -> Function<'bump>;
}

pub trait MaybeEvaluatable<'bump> {
    fn get_evaluated(&self) -> Option<Function<'bump>>;
}

impl<'bump, I> MaybeEvaluatable<'bump> for I where I:Evaluatable<'bump> {
    fn get_evaluated(&self) -> Option<Function<'bump>> {
        Some(self.get_evaluated())
    }
}

impl<'bump, I> MaybeEvaluatable<'bump> for Option<I> where I: MaybeEvaluatable<'bump> {
    fn get_evaluated(&self) -> Option<Function<'bump>> {
        self.as_ref().and_then(MaybeEvaluatable::get_evaluated)
    }
}