//! The [Error] type use thoughout the tool
//!
//! This type is an efficient wrapping of [BaseError] to get [Location] information,
//! gather a backtrace and crash early in debug mode.
//!
//! The location information is handeled by [Location] which wraps the [Locate] trait.
//! This lets us give hints to the user about where in the input file an error might be
//! comming from. This information is optionnal (in that case use `()` as location)
//!
//! In debug mode build an [Error] makes the tool panic as fast as possible, this way
//! we can more easily take advantage of the debuging tool and figure out where the error
//! is comming from. Conversally, in `release` mode, the tool is expected to never crash
//! and only bubble up [Error].
//!
//! The [result] module give a access to something quite similar to `anyhow`'s [`Context`](https://docs.rs/anyhow/latest/anyhow/trait.Context.html)
//! trait.

use std::fmt::Display;

#[allow(clippy::module_inception)]
mod error;
mod macros;

pub use error::Error;

mod inner_error;

mod location;
pub use location::{Locate, LocateHelper, Location, LocationProvider};

mod result;
pub use result::{BaseContext, CVContext, ExtraOption};

mod anywhere;
pub use anywhere::Anywhere;

use crate::formula::function::signature::CheckError;
use crate::formula::sort::sort_proxy::InferenceError;

// pub type CVResult<T, L> = std::result::Result<T, Error<L>>;

/// useful shortcut
pub type Result<T> = std::result::Result<T, Error>;
pub type Unit = crate::Result<()>;

/// The main error type.
///
/// This is expected to mainly gather other error types in a sort of dynamic dispatch.
///
/// Implementing [Into<BaseError>] gives the implementation of [Into<Error>]. And thus the
/// possibility to use `?`. This is the expected way to add new error types (beside expending
/// the enum)
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
    BuilderError(#[from] Box<dyn std::error::Error + Sync + Send>),
    #[error(transparent)]
    CheckError(#[from] CheckError),
    #[error(transparent)]
    GraphError(#[from] crate::problem::cell_dependancies::GraphError),
    #[error(transparent)]
    AssertionError(#[from] AssertionError),
    #[error(transparent)]
    RunnerError(#[from] crate::runner::RunnerError),
    #[error(transparent)]
    JsonError(#[from] serde_json::Error),

    #[error("unknown {kind} {name}")]
    UnknownSymbol { kind: String, name: String },
    #[error("duplicate {kind} {name}")]
    DuplicateSymbol { kind: String, name: String },

    #[error(transparent)]
    ParsingError(#[from] crate::parser::error::ParsingError),

    // some joker when we don't want to make a new type
    // this lets us emulate the [`anyhow`](https://docs.rs/anyhow/latest/anyhow/)
    // crate in some ways
    #[error("reason: {}", .0)]
    Message(String),
    #[error("reason: {0}\ncomming from: {1}")]
    MessageAndError(String, #[source] Box<dyn std::error::Error + Sync + Send>),
}

#[derive(Debug, thiserror::Error)]
#[error("asserting error: {0}")]
pub struct AssertionError(pub String);

impl BaseError {
    pub fn strict_with(self, location: Location) -> Error {
        // Error::new(inner_error::InnerError::new(location, self))
        Error::new(location, self)
    }

    pub fn strict_to_err<T>(self, location: Location) -> Result<T> {
        Error::err(location, self)
    }

    /// a shortcut to crash declare duplicates symbols
    pub fn duplicate_symbol(kind: &impl Display, name: &impl Display) -> Self {
        Self::DuplicateSymbol {
            kind: kind.to_string(),
            name: name.to_string(),
        }
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

impl From<nom::Err<()>> for BaseError {
    fn from(value: nom::Err<()>) -> Self {
        use crate::runner::RunnerError;
        RunnerError::from(value).into()
    }
}
