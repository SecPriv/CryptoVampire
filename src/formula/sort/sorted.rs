use super::{sort::Sort};
use thiserror::Error;

pub trait Sorted {
    fn sort<'a>(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError>;
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
