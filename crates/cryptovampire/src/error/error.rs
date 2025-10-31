use std::backtrace::Backtrace;
use std::fmt::{Debug, Display};

use super::inner_error::InnerError;
use super::{BaseError, Locate, Location, LocationProvider, Result};

/// The main error type of cryptovampire, designed to have a light footprint
///
/// To implement [Into<Error>] prefer going though [super::BaseError]
#[derive(Debug)]
pub struct Error(Box<InnerError>);

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let location = self.get_location();
        let backtrace = self.get_backtrace();
        let err = self.get_error();
        location.location_fmt(err, backtrace, f)
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
    /// build a new [Error]. Always panics in debug mode.
    ///
    /// anything building an [Error] should call this function.
    pub fn new(location: Location, error: BaseError) -> Self {
        let inner = InnerError::new(location, error);
        let r = Error(Box::new(inner));

        if cfg!(debug_assertions) {
            panic!("encountered error in debug mode: aborting...\n{r}")
        } else {
            r
        }
    }

    /// Same as [Self::new] but returns a [Result] instead
    pub fn err<T>(location: Location, error: BaseError) -> Result<T> {
        Err(Self::new(location, error))
    }

    pub fn from_err<T, P: LocationProvider>(location: P, error: impl Into<BaseError>) -> Result<T> {
        Self::err(location.provide(), error.into())
    }

    pub fn get_location(&self) -> &Location {
        &self.0.location
    }

    pub fn get_error(&self) -> &BaseError {
        &self.0.error
    }

    pub fn get_backtrace(&self) -> Option<&Backtrace> {
        self.0.backtrace.as_ref()
    }

    pub(crate) fn set_location(mut self, l: Location) -> Self {
        self.0.location = l;
        self
    }

    /// shortuct to simply output an error with a message
    ///
    /// Using the macros is proably better in this case
    pub fn msg_with_location(location: Location, str: String) -> Self {
        let error = BaseError::Message(str);
        Self::new(location, error)
    }
}

impl<U> From<U> for Error
where
    U: Into<BaseError>,
{
    fn from(value: U) -> Self {
        crate::Error::new(Default::default(), value.into())
    }
}
