use std::fmt::Debug;

use thiserror::Error;

use crate::{environement::traits::KnowsRealm, formula::function::signature::CheckError};

use super::Sort;

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
}

impl<'bump> From<CheckError<'bump>> for SortedError {
    fn from(value: CheckError<'bump>) -> Self {
        match value {
            CheckError::WrongNumberOfArguments { got, expected } => Self::WrongArguments {
                expected: format!("{expected:?}"),
                got: format!("{got:?}"),
            },
            e @ CheckError::SortError { .. } => Self::InferenceError {
                msg: format!("{e:?}"),
            },
        }
    }
}
