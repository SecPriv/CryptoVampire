use std::{fmt::Display, iter};

use thiserror::Error;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Error)]
pub enum WrongLengthError {
    #[error("too many items")]
    TooMany,
    #[error("not enough items")]
    NotEnough,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Error, Default)]
pub struct NotEnoughItemError();

impl Display for NotEnoughItemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "not enough items")
    }
}

impl From<NotEnoughItemError> for WrongLengthError {
    fn from(value: NotEnoughItemError) -> Self {
        WrongLengthError::NotEnough
    }
}

pub trait IntoArray<U> {
    fn into_array<const N: usize>(
        self,
    ) -> Result<([U; N], impl Iterator<Item = U>), NotEnoughItemError>;

    fn into_array_exact<const N: usize>(self) -> Result<[U; N], WrongLengthError>
    where
        Self: Sized,
    {
        let (arr, mut leftover) = self.into_array()?;
        if let Some(_) = leftover.next() {
            Err(WrongLengthError::TooMany)
        } else {
            Ok(arr)
        }
    }
}

impl<I, U> IntoArray<U> for I
where
    I: IntoIterator<Item = U>,
{
    fn into_array<const N: usize>(
        self,
    ) -> Result<([U; N], impl Iterator<Item = U>), NotEnoughItemError> {
        let mut iter = self.into_iter();
        let mut vec = Vec::with_capacity(N);
        vec.extend(iter.by_ref().take(N));
        let arr = vec.try_into();
        match arr {
            Ok(arr) => Ok((arr, iter)),
            Err(_) => Err(NotEnoughItemError()),
        }
    }
}
