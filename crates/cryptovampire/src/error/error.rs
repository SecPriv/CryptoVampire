use std::{
    backtrace::Backtrace,
    fmt::{Debug, Display},
};

use serde::{Deserialize, Serialize};

use super::{
    inner_error::InnerError,
    location::{Location, OwnedSpan},
    BaseError, CVResult,
};

#[derive(Debug)]
pub struct Error<L>(Box<InnerError<L>>);

impl<U> Display for Error<U>
where
    U: Location,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Location::location_fmt(self, f)
    }
}

impl<L: Location> std::error::Error for Error<L> {
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match &self.0.error {
            BaseError::PestError(e) => Some(e),
            BaseError::IO(e) => Some(e),
            _ => None,
        }
    }
}

impl<L: Location> Error<L> {
    pub fn new(location: L, error: BaseError) -> Self {
        let inner = InnerError::new(location, error);
        let r = Error(Box::new(inner));

        if cfg!(debug_assertions) {
            Err(r).expect("debug is on, giving up")
        } else {
            r
        }
    }

    pub fn err<T>(location: L, error: BaseError) -> CVResult<T, L> {
        Err(Self::new(location, error))
    }

    pub fn from_err<T, FU>(
        location: impl FnOnce() -> FU,
        error: impl Into<BaseError>,
    ) -> CVResult<T, L>
    where
        FU: Into<L>,
    {
        Self::err(location().into(), error.into())
    }

    pub(crate) fn get_location(&self) -> &L {
        &self.0.location
    }

    pub(crate) fn get_error(&self) -> &BaseError {
        &self.0.error
    }

    pub(crate) fn get_backtrace(&self) -> Option<&Backtrace> {
        self.0.backtrace.as_ref()
    }
}
