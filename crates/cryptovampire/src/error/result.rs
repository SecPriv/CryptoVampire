use super::{inner_error::InnerError, CVResult};

pub trait CVContext<T, L> {
    fn with_location(self, location: impl Into<L>) -> CVResult<T, L>;
}

impl<T, E, L> CVContext<T, L> for Result<T, E>
where
    super::BaseError: From<E>,
    L: crate::Location
{
    fn with_location(self, location: impl Into<L>) -> CVResult<T, L> {
        match self {
            Ok(x) => Ok(x),
            Err(error) => crate::Error::err(location.into(), error.into()),
        }
    }
}
