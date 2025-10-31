use std::fmt::Display;

use super::runner::DiscovererError;
use super::runners::{HandlerError, RunnersCreationError};

/// Errors related to the interaction with a solver
#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum RunnerError {
    #[error(transparent)]
    DiscovererError(#[from] DiscovererError),
    #[error(transparent)]
    RunnersCreationError(#[from] RunnersCreationError),
    #[error(transparent)]
    HandlerError(#[from] HandlerError),

    #[error("error while parsing a solver's ouptut: {0}")]
    ParsingError(#[from] ParsingError),

    #[error("ran out of tries (tried {0} times)")]
    RanOutOfTries(u32),
    #[error("nothing to do: {0}")]
    NothingToDo(String),

    #[error(
        "unexpected behaviour while running {tool}:\nran: \"{cmd:?}\"\nreturn code: \
         {return_code}\nstdout:\n{stdout}"
    )]
    UnexpectedResult {
        tool: &'static str,
        return_code: i32,
        cmd: std::process::Command,
        stdout: String,
    },

    #[error("disproved the query")]
    Disprove,
}

#[non_exhaustive]
#[derive(Debug, thiserror::Error)]
pub enum ParsingError {
    #[error(transparent)]
    Tptp(nom::Err<()>),
}

impl RunnerError {
    pub fn nothing_to_do(d: impl Display) -> Self {
        Self::NothingToDo(d.to_string())
    }
}

impl From<nom::Err<()>> for RunnerError {
    fn from(value: nom::Err<()>) -> Self {
        RunnerError::ParsingError(ParsingError::Tptp(value))
    }
}
