use std::fmt::Display;

use serde::{Deserialize, Serialize};

mod error;

pub use error::Error;

mod inner_error;

mod location;
pub use location::OwnedSpan;

mod result;
pub use result::CVContext;

pub type CVResult<T, L> = std::result::Result<T, Error<L>>;

#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum BaseError {
    #[error("typing error")]
    TypingError,
    #[error("{:}", .0)]
    PestErrorVariant(pest::error::ErrorVariant<crate::parser::Rule>),
    #[error(transparent)]
    PestError(#[from] pest::error::Error<crate::parser::Rule>),
    #[error(transparent)]
    IO(#[from] std::io::Error),
}

impl BaseError {
    pub fn with<L>(self, location: L) -> Error<L> {
        Error::new(inner_error::InnerError::new(location, self))
    }

    pub fn to_err<T, L>(self, location: L) -> CVResult<T, L> {
        Err(self.with(location))
    }
}
