mod ast;
mod parser;
// mod builders;

use pest::{error::Error, Span};
use pest_derive::Parser;

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

#[inline(always)]
/// imediadly crashes in debug mode (to get the stacktrace and everything)
/// it properly bubles up the error in release mode
fn err<E: std::error::Error, T>(err: E) -> Result<T, E> {
    if cfg!(debug_assertions) {
        Err(err).unwrap()
    } else {
        Err(err)
    }
}

macro_rules! merr {
    ($span:expr; $msg:literal $(,$args:expr)*) => {
        pest::error::Error::new_from_span(
            pest::error::ErrorVariant::CustomError {
                message: format!($msg $(,$args)*),
            },
            $span,
        )
    };
}

pub(crate) use merr;

use crate::formula::sort::sort_proxy::InferenceError;

trait IntoRuleResult<T, Err> {
    fn into_rr<'a>(self, span: Span<'a>) -> Result<T, E>;
}

impl<'bump, T> IntoRuleResult<T, InferenceError<'bump>> for Result<T, InferenceError<'bump>> {
    fn into_rr<'a>(self, span: Span<'a>) -> Result<T, E> {
        match self {
            Ok(x) => Ok(x),
            Err(e) => err(merr!(span; "{}", e)),
        }
    }
}
