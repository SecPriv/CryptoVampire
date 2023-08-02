use std::ops::RangeInclusive;

use thiserror::Error;

use crate::{formula::sort::sort_proxy::InferenceError, utils::infinity::Infinity};

#[derive(Debug, PartialEq, Eq, Clone, Error)]
pub enum CheckError<'bump> {
    #[error("wrong number of arguments (got {got}, expected in [{}, {}])", .expected.start(), .expected.end())]
    WrongNumberOfArguments {
        got: Infinity<usize>,
        expected: RangeInclusive<Infinity<usize>>,
    },
    #[error("unsolvable sort problem at position {position:?}, caused by {error}")]
    SortError {
        position: Option<usize>,
        error: InferenceError<'bump>,
    },
}

impl<'bump> CheckError<'bump> {
    pub fn from_inference(error: InferenceError<'bump>, position: Option<usize>) -> Self {
        Self::SortError { position, error }
    }
}

