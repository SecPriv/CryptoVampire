use std::fmt::{Debug, Display};

use serde::{Deserialize, Serialize};

use super::{inner_error::InnerError, location::OwnedSpan, BaseError};

#[derive(Debug)]
pub struct Error<L>(Box<InnerError<L>>);

impl Display for Error<()> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0.error, f)?;
        match &self.0.backtrace {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

impl Display for Error<OwnedSpan> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let span = self.0.location.as_span();
        let pest_error = match &self.0.error {
            BaseError::PestErrorVariant(variant) => {
                &pest::error::Error::new_from_span(variant.clone(), span)
            }
            BaseError::PestError(e) => e,
            e => {
                let variant = pest::error::ErrorVariant::<crate::parser::Rule>::CustomError {
                    message: e.to_string(),
                };
                &pest::error::Error::new_from_span(variant, span)
            }
        };
        Display::fmt(pest_error, f)?;
        match &self.0.backtrace {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

impl<L> std::error::Error for Error<L>
where
    Error<L>: Display,
    L: Debug,
{
    fn cause(&self) -> Option<&dyn std::error::Error> {
        match &self.0.error {
            BaseError::PestError(e) => Some(e),
            BaseError::IO(e) => Some(e),
            _ => None,
        }
    }
}

impl<L> Error<L> {
    pub fn new(inner: InnerError<L>) -> Self {
        Self(Box::new(inner))
    }
}
