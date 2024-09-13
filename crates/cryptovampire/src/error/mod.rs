use std::fmt::Display;

use serde::{Deserialize, Serialize};

mod error;

pub use error::Error;

mod inner_error;

mod location;
pub use location::{OwnedSpan, Location, WithHasLocation, HasLocation, SelfLocation};

mod result;
pub use result::CVContext;

use crate::formula::sort::sort_proxy::InferenceError;

pub type CVResult<T, L> = std::result::Result<T, Error<L>>;

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
}

impl BaseError {
    pub fn strict_with<L:crate::Location>(self, location: L) -> Error<L>
    {
        // Error::new(inner_error::InnerError::new(location, self))
        Error::new(location, self)
    }

    pub fn strict_to_err<T, L:crate::Location>(self, location: L) -> CVResult<T, L>
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