use super::Result;
use super::location::LocationProvider;

pub trait CVContext<T> {
    fn with_location<P: LocationProvider>(self, location: P) -> Result<T>;

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

    fn no_location(self) -> Result<T>
    where
        Self: Sized,
    {
        self.with_location(())
    }
}

pub trait BaseContext<T> {
    fn with_context<D>(self, location: impl LocationProvider, f: impl FnOnce() -> D) -> Result<T>
    where
        D: std::fmt::Display;

    fn with_message<D: std::fmt::Display>(self, f: impl FnOnce() -> D) -> Result<T>
    where
        Self: Sized,
    {
        self.with_context((), f)
    }
}

impl<T, E> CVContext<T> for std::result::Result<T, E>
where
    super::BaseError: From<E>,
{
    fn with_location<P: LocationProvider>(self, location: P) -> Result<T> {
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
    fn with_location<P: LocationProvider>(self, location: P) -> Result<T> {
        crate::Error::err(location.provide(), self.into())
    }
}

impl<T, E: std::error::Error + Send + Sync + 'static> BaseContext<T> for std::result::Result<T, E> {
    fn with_context<D>(self, location: impl LocationProvider, f: impl FnOnce() -> D) -> Result<T>
    where
        D: std::fmt::Display,
    {
        match self {
            Ok(x) => Ok(x),
            Err(error) => crate::Error::err(
                location.provide(),
                super::BaseError::MessageAndError(f().to_string(), Box::new(error)),
            ),
        }
    }
}

impl<T> BaseContext<T> for Option<T> {
    fn with_context<D>(self, location: impl LocationProvider, f: impl FnOnce() -> D) -> Result<T>
    where
        D: std::fmt::Display,
    {
        match self {
            Some(x) => Ok(x),
            None => crate::Error::err(
                location.provide(),
                super::BaseError::Message(f().to_string()),
            ),
        }
    }
}

pub trait ExtraOption<T> {
    fn unknown_symbol(
        self,
        location: impl LocationProvider,
        kind: &impl std::fmt::Display,
        name: &impl std::fmt::Display,
    ) -> crate::Result<T>;
}

impl<T> ExtraOption<T> for Option<T> {
    fn unknown_symbol(
        self,
        location: impl LocationProvider,
        kind: &impl std::fmt::Display,
        name: &impl std::fmt::Display,
    ) -> crate::Result<T> {
        self.ok_or_else(|| {
            crate::Error::new(
                location.provide(),
                super::BaseError::UnknownSymbol {
                    kind: kind.to_string(),
                    name: name.to_string(),
                },
            )
        })
    }
}
