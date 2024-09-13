use super::{inner_error::InnerError, CVResult};

pub trait CVContext<T, L> {
    fn with_location(self, location: impl Into<L>) -> CVResult<T, L>;
}

impl<T, E, L> CVContext<T, L> for Result<T, E>
where
    super::BaseError: From<E>,
{
    fn with_location(self, location: impl Into<L>) -> CVResult<T, L> {
        match self {
            Ok(x) => Ok(x),
            Err(err) => Err(super::Error::new(InnerError::new(
                location.into(),
                err.into(),
            ))),
        }
    }
}
