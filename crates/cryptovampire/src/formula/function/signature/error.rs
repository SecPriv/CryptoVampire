use std::ops::RangeInclusive;

use thiserror::Error;
use utils::infinity::Infinity;

use crate::formula::sort::sort_proxy::InferenceError;

#[derive(Debug, PartialEq, Eq, Clone, Error)]
pub enum CheckError {
    #[error("wrong number of arguments (got {got}, expected in [{}, {}])", .expected.start(), .expected.end())]
    WrongNumberOfArguments {
        got: Infinity<usize>,
        expected: RangeInclusive<Infinity<usize>>,
    },
    #[error("unsolvable sort problem at position {position:?}, caused by {error}")]
    SortError {
        position: Option<usize>,
        #[source]
        error: InferenceError,
    },
}

impl CheckError {
    pub fn from_inference(error: InferenceError, position: Option<usize>) -> Self {
        Self::SortError { position, error }
    }
    pub fn wrong_num_args<Idx: Into<Infinity<usize>>>(
        got: Idx,
        expected: RangeInclusive<Idx>,
    ) -> Self {
        let (start, end) = expected.into_inner();
        Self::WrongNumberOfArguments {
            got: got.into(),
            expected: start.into()..=end.into(),
        }
    }
}
