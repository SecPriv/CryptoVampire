use super::{inner_error::InnerError, location::LocationProvider, Result};

pub trait CVContext<T> {
    fn with_location<P: LocationProvider>(
        self,
        location: impl FnOnce() -> P,
    ) -> Result<T>;

    fn with_pre_location<L: crate::error::LocateHelper, S: std::fmt::Display>(
        self,
        location: &L,
        str: &S,
    ) -> Result<T>
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
    fn with_location< P: LocationProvider>(
        self,
        location: impl FnOnce() -> P,
    ) -> Result<T> {
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
    fn with_location<P: LocationProvider>(
        self,
        location: impl FnOnce() -> P,
    ) -> Result<T> {
        crate::Error::err(location().provide(), self.into())
    }
}
