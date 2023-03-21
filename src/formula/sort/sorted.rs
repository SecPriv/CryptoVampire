use std::fmt::Display;

use thiserror::Error;

use super::Sort;


pub trait Sorted<'a> {
    fn sort(&self, args: &[Sort<'a>]) -> Result<Sort<'a>, SortedError>;
}

#[derive(Debug, Error)]
pub enum SortedError {
    #[error("wrong number of arguments (expected {expected}, got {got})")]
    WrongArguments {
        expected: Option<Box<dyn Display>>,
        got: Option<Box<dyn Display>>,
    },
    #[error("the sort cannot be deduced")]
    Impossible,
}
