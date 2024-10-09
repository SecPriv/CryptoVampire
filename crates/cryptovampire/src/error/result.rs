use super::{inner_error::InnerError, location::LocationProvider, CVResult};

pub trait CVContext<T> {
    fn with_location< L: crate::Location>(self, location: impl LocationProvider<L>) -> CVResult<T, L>;
}

impl<T, E> CVContext<T> for Result<T, E>
where
    super::BaseError: From<E>,
{
    fn with_location< L: crate::Location>(self, location: impl LocationProvider<L>) -> CVResult<T, L> {
        match self {
            Ok(x) => Ok(x),
            Err(error) => crate::Error::err(location.provide(), error.into()),
        }
    }
}

impl<T, E> CVContext<T> for E
where
    E: Into<super::BaseError>,
{
    fn with_location< L: crate::Location>(self, location: impl LocationProvider<L>) -> CVResult<T, L> {
        crate::Error::err(location.provide(), self.into())
    }
}
