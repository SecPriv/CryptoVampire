use std::fmt::Display;

use serde::{Deserialize, Serialize};

mod error;
mod macros;

pub use error::Error;

mod inner_error;

mod location;
pub use location::{Location, LocationProvider, LocateHelper, Locate};

mod result;
pub use result::{CVContext, ExtraOption};

mod anywhere;
pub use anywhere::Anywhere;

use crate::formula::sort::sort_proxy::InferenceError;

// pub type CVResult<T, L> = std::result::Result<T, Error<L>>;

pub type Result<T> = std::result::Result<T, Error>;
pub type Unit = crate::Result<()>;

#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum BaseError {
    #[error(transparent)]
    TypingError(#[from] InferenceError),
    #[error("{:}", .0)]
    PestErrorVariant(pest::error::ErrorVariant<crate::parser::Rule>),
    #[error(transparent)]
    PestError(#[from] pest::error::Error<crate::parser::Rule>),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error("BuilderError: {0}")]
    BuilderError(#[from] Box<dyn std::error::Error>),

    #[error("unknown {kind} {name}")]
    UnknownSymbol{
        kind: String,
        name: String
    },

    #[error(transparent)]
    ParsingError(#[from] crate::parser::error::ParsingError),

    #[error("reason: {}", .0)]
    Message(String)
}

impl BaseError {
    pub fn strict_with(self, location: Location) -> Error
    {
        // Error::new(inner_error::InnerError::new(location, self))
        Error::new(location, self)
    }

    pub fn strict_to_err<T>(self, location: Location) -> Result<T>
    {
        Error::err(location, self)
    }
}

impl From<crate::formula::sort::sort_proxy::UpdateError> for BaseError {
    fn from(value: crate::formula::sort::sort_proxy::UpdateError) -> Self {
        InferenceError::from(value).into()
    }
}

impl From<pest::error::ErrorVariant<crate::parser::Rule>> for BaseError {
    fn from(value: pest::error::ErrorVariant<crate::parser::Rule>) -> Self {
        BaseError::PestErrorVariant(value)
    }
}

impl<'a> From<&'a str> for BaseError {
    fn from(value: &'a str) -> Self {
        Self::Message(value.into())
    }
}
