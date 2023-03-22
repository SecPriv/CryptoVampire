// use core::slice::SlicePattern;

use super::{
    sort::{
        builtins::{BOOL, MESSAGE},
        Sort,
    },
    variable::Variable,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier<'bump> {
    Exists { variables: Vec<Variable<'bump>> },
    Forall { variables: Vec<Variable<'bump>> },
    // FindSuchThat { variables: Vec<Variable<'bump>> },
}

impl<'bump> Quantifier<'bump> {
    pub fn get_output_sort(&self) -> Sort<'bump> {
        // match self {
        //     Quantifier::Exists { variables: _ } => BOOL.as_ref(),
        //     Quantifier::Forall { variables: _ } => BOOL.as_ref(),
        //     // Quantifier::FindSuchThat { variables: _ } => MESSAGE.as_ref(),
        // }
        BOOL.as_sort()
    }

    pub fn get_variables(&self) -> &[Variable<'bump>] {
        match self {
            Quantifier::Exists { variables }
            | Quantifier::Forall { variables }
            /* | Quantifier::FindSuchThat { variables } */ => variables.as_slice(),
        }
    }
}
