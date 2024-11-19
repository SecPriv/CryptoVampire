use std::{
    backtrace::Backtrace,
    fmt::{Debug, Display},
};

use serde::{Deserialize, Serialize};

use super::{
    inner_error::InnerError, BaseError, Location, LocationProvider, Result
};


#[derive(Debug)]
pub struct Error(Box<InnerError>);

impl Display for Error
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Location::location_fmt(self, f)
    }
}

impl std::error::Error for Error {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match &self.0.error {
            BaseError::PestError(e) => Some(e),
            BaseError::IO(e) => Some(e),
            BaseError::TypingError(e) => Some(e),
            _ => None,
        }
    }
}

impl Error {
    pub fn new(location: Location, error: BaseError) -> Self {
        let inner = InnerError::new(location, error);
        let r = Error(Box::new(inner));

        if cfg!(debug_assertions) {
            Err(r).expect("debug is on, giving up")
        } else {
            r
        }
    }

    pub fn err<T>(location: Location, error: BaseError) -> Result<T> {
        Err(Self::new(location, error))
    }

    pub fn from_err<T, P:LocationProvider>(
        location: impl FnOnce() -> P,
        error: impl Into<BaseError>,
    ) -> Result<T>
    {
        Self::err(location().provide(), error.into())
    }

    pub(crate) fn get_location(&self) -> &Location {
        &self.0.location
    }

    pub(crate) fn get_error(&self) -> &BaseError {
        &self.0.error
    }

    pub(crate) fn get_backtrace(&self) -> Option<&Backtrace> {
        self.0.backtrace.as_ref()
    }

}
