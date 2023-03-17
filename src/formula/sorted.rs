use super::{sort::Sort};
use thiserror::Error;

pub trait Sorted {
    fn sort(&self, args: &[impl Sorted]) -> Result<Sort, SortedError>;
}


#[derive(Debug, Error)]
pub enum SortedError {
    #[error("wrong number of arguments (expected {expected:?}, got {got:?})")]
    WrongNumberOfArguments{
        expected: Option<usize>,
        got: Option<usize>
    },
    #[error("the sort cannot be deduced")]
    Impossible
}
