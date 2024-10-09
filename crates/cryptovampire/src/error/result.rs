use super::{inner_error::InnerError, location::LocationProvider, CVResult};

pub trait CVContext<T> {
    fn with_location<L: crate::Location, P: LocationProvider<L>>(
        self,
        location: impl FnOnce() -> P,
    ) -> CVResult<T, L>;

    fn with_pre_location<L: crate::PreLocation, S: std::fmt::Display>(
        self,
        location: L,
        str: &S,
    ) -> CVResult<T, L::L>
    where
        Self: Sized,
    {
        self.with_location(|| location.help_provide(str))
    }
}

impl<T, E> CVContext<T> for std::result::Result<T, E>
where
    super::BaseError: From<E>,
{
    fn with_location<L: crate::Location, P: LocationProvider<L>>(
        self,
        location: impl FnOnce() -> P,
    ) -> CVResult<T, L> {
        match self {
            Ok(x) => Ok(x),
            Err(error) => crate::Error::err(location().provide(), error.into()),
        }
    }
}

impl<T, E> CVContext<T> for E
where
    E: Into<super::BaseError>,
{
    fn with_location<L: crate::Location, P: LocationProvider<L>>(
        self,
        location: impl FnOnce() -> P,
    ) -> CVResult<T, L> {
        crate::Error::err(location().provide(), self.into())
    }
}
