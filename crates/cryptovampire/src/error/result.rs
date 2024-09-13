use super::{inner_error::InnerError, CVResult, HasLocation, SelfLocation};

pub trait CVContext<T> {
    fn with_location<U, L: crate::Location>(self, location: impl FnOnce() -> U) -> CVResult<T, L>
    where
        U: Into<L>;

    fn with_has_location<W>(self, with_location: &W) -> CVResult<T, SelfLocation<W>>
    where
        W: HasLocation,
        Self: Sized,
    {
        self.with_location(|| with_location.get_location())
    }
}

impl<T, E> CVContext<T> for Result<T, E>
where
    super::BaseError: From<E>,
{
    fn with_location<U, L: crate::Location>(self, location: impl FnOnce() -> U) -> CVResult<T, L>
    where
        U: Into<L>,
    {
        match self {
            Ok(x) => Ok(x),
            Err(error) => crate::Error::err(location().into(), error.into()),
        }
    }
}
