use std::fmt::Display;

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
    fn from(_: NotEnoughItemError) -> Self {
        WrongLengthError::NotEnough
    }
}

pub trait IntoArray<U, A> {
    // fn into_array<const N: usize>(
    //     self,
    // ) -> Result<([U; N], impl Iterator<Item = U>), NotEnoughItemError>;

    // fn into_array_exact<const N: usize>(self) -> Result<[U; N], WrongLengthError>
    // where
    //     Self: Sized,
    // {
    //     let (arr, mut leftover) = self.into_array()?;
    //     if let Some(_) = leftover.next() {
    //         Err(WrongLengthError::TooMany)
    //     } else {
    //         Ok(arr)
    //     }
    // }
    fn collect_array(self) -> Result<(A, impl Iterator<Item = U>), NotEnoughItemError>;
    fn collect_array_exact(self) -> Result<A, WrongLengthError>
    where
        Self: Sized,
    {
        let (arr, mut leftover) = self.collect_array()?;
        if leftover.next().is_some() {
            Err(WrongLengthError::TooMany)
        } else {
            Ok(arr)
        }
    }
}

impl<I, U, const N: usize> IntoArray<U, [U; N]> for I
where
    I: IntoIterator<Item = U>,
{
    fn collect_array(self) -> Result<([U; N], impl Iterator<Item = U>), NotEnoughItemError> {
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

impl<I, U, E, const N: usize> IntoArray<U, Result<[U; N], E>> for I
where
    I: IntoIterator<Item = Result<U, E>>,
{
    fn collect_array(
        self,
    ) -> Result<(Result<[U; N], E>, impl Iterator<Item = U>), NotEnoughItemError> {
        let mut iter = self.into_iter();
        let vec: Result<Vec<_>, E> = iter.by_ref().take(N).collect();
        let iter = iter.filter_map(|x| x.ok());
        match vec {
            Err(e) => Ok((Err(e), iter)),
            Ok(vec) => match vec.try_into() {
                Ok(arr) => Ok((Ok(arr), iter)),
                Err(_) => Err(NotEnoughItemError()),
            },
        }
    }
}

impl<I, U, const N: usize> IntoArray<U, Option<[U; N]>> for I
where
    I: IntoIterator<Item = Option<U>>,
{
    fn collect_array(
        self,
    ) -> Result<(Option<[U; N]>, impl Iterator<Item = U>), NotEnoughItemError> {
        let mut iter = self.into_iter();
        let vec: Option<Vec<_>> = iter.by_ref().take(N).collect();
        let iter = iter.flatten();
        match vec {
            None => Ok((None, iter)),
            Some(vec) => match vec.try_into() {
                Ok(arr) => Ok((Some(arr), iter)),
                Err(_) => Err(NotEnoughItemError()),
            },
        }
    }
}
