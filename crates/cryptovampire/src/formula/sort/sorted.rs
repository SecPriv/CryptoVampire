use std::fmt::Debug;

use thiserror::Error;

use super::Sort;
use crate::formula::function::signature::CheckError;

pub trait Sorted<'a> {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError>;
}

#[derive(Debug, Error)]
pub enum SortedError {
    #[error("wrong number of arguments (expected {expected:?}, got {got:?})")]
    WrongArguments { expected: String, got: String },
    #[error("the sort cannot be deduced")]
    Impossible,
    #[error("wrong argument")]
    InferenceError { msg: String },
    #[error(transparent)]
    CheckError(#[from] CheckError),
}

// impl<'bump> From<CheckError> for SortedError {
//     fn from(value: CheckError) -> Self {
//         match value {
//             CheckError::WrongNumberOfArguments { got, expected } => Self::WrongArguments {
//                 expected: format!("{expected:?}"),
//                 got: format!("{got:?}"),
//             },
//             e @ CheckError::SortError { .. } => Self::InferenceError {
//                 msg: format!("{e:?}"),
//             },
//         }
//     }
// }
