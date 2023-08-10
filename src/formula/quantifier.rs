// use core::slice::SlicePattern;

use std::sync::Arc;

use crate::implvec;

use super::{
    sort::{
        builtins::{BOOL, CONDITION},
        Sort,
    },
    variable::Variable,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Quantifier<'bump> {
    Exists {
        // status: Status,
        variables: Arc<[Variable<'bump>]>,
    },
    Forall {
        // status: Status,
        variables: Arc<[Variable<'bump>]>,
    },
    // FindSuchThat { variables: Vec<Variable<'bump>> },
}

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
// pub enum Status {
//     Condition,
//     Bool,
// }

// impl Default for Status {
//     fn default() -> Self {
//         Self::Bool
//     }
// }

// impl Status {
//     /// Returns `true` if the status is [`Condition`].
//     ///
//     /// [`Condition`]: Status::Condition
//     #[must_use]
//     pub fn is_condition(&self) -> bool {
//         matches!(self, Self::Condition)
//     }

//     /// Returns `true` if the status is [`Bool`].
//     ///
//     /// [`Bool`]: Status::Bool
//     #[must_use]
//     pub fn is_bool(&self) -> bool {
//         matches!(self, Self::Bool)
//     }
// }

// impl Into<Sort<'static>> for Status {
//     fn into(self) -> Sort<'static> {
//         match self {
//             Status::Condition => CONDITION.clone(),
//             Status::Bool => BOOL.clone(),
//         }
//     }
// }

impl<'bump> Quantifier<'bump> {
    pub fn get_output_sort(&self) -> Sort<'bump> {
        // match self {
        //     Quantifier::Exists { variables: _ } => BOOL.as_ref(),
        //     Quantifier::Forall { variables: _ } => BOOL.as_ref(),
        //     // Quantifier::FindSuchThat { variables: _ } => MESSAGE.as_ref(),
        // }
        // self.status().into()
        BOOL.as_sort()
    }

    pub fn get_variables(&self) -> &Arc<[Variable<'bump>]> {
        match self {
            Quantifier::Exists { variables, .. }
            | Quantifier::Forall { variables ,..}
            /* | Quantifier::FindSuchThat { variables } */ => variables,
        }
    }

    // pub fn status(&self) -> Status {
    //     match self {
    //         Self::Exists { status, .. } | Self::Forall { status, .. } => *status,
    //     }
    // }

    pub fn exists(variables: implvec!(Variable<'bump>)) -> Self {
        Self::Exists {
            variables: variables.into_iter().collect(),
            // status: Status::Bool,
        }
    }

    pub fn forall(variables: implvec!(Variable<'bump>)) -> Self {
        Self::Forall {
            variables: variables.into_iter().collect(),
            // status: Status::Bool,
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Quantifier::Exists { .. } => "exist",
            Quantifier::Forall { .. } => "forall",
        }
    }
}

fn enlarge<'a, 'b>(q: Quantifier<'a>) -> Quantifier<'b>
where
    'a: 'b,
{
    q
}
