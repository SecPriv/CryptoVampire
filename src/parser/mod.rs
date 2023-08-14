mod ast;
mod parser;
// mod builders;

use std::ops::Index;

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

fn merr<'a>(s: Span<'a>, msg: String) -> E {
    pest::error::Error::new_from_span(pest::error::ErrorVariant::CustomError { message: msg }, s)
}

// macro_rules! merr {
//     ($span:expr; $msg:literal $(,$args:expr)*) => {
//         pest::error::Error::new_from_span(
//             pest::error::ErrorVariant::CustomError {
//                 message: format!($msg $(,$args)*),
//             },
//             $span,
//         )
//     };
// }

// pub(crate) use merr;

use crate::{
    f,
    formula::{function::signature::CheckError, sort::sort_proxy::InferenceError},
};

trait IntoRuleResult<T, Err> {
    fn into_rr<'a>(self, span: Span<'a>) -> Result<T, E>;
}

impl<'bump, T> IntoRuleResult<T, InferenceError<'bump>> for Result<T, InferenceError<'bump>> {
    fn into_rr<'a>(self, span: Span<'a>) -> Result<T, E> {
        match self {
            Ok(x) => Ok(x),
            Err(e) => err(merr(span, f!("{}", e))),
        }
    }
}

trait IntoRuleResultFunction<T, Err> {
    fn into_rr<'a, I>(self, fun: Span<'a>, args: I) -> Result<T, E>
    where
        I: Index<usize, Output = Span<'a>>;
}

impl<'bump, T> IntoRuleResultFunction<T, CheckError<'bump>> for Result<T, CheckError<'bump>> {
    fn into_rr<'a, I>(self, fun: Span<'a>, args: I) -> Result<T, E>
    where
        I: Index<usize, Output = Span<'a>>,
    {
        self.map_err(|err| match err {
            CheckError::WrongNumberOfArguments { got, expected } => merr(
                fun,
                format!("wring number of arguments: expected {expected:?}, got {got}"),
            ),
            CheckError::SortError {
                position: None,
                error,
            } => merr(fun, f!("{error}")),
            CheckError::SortError {
                position: Some(idx),
                error,
            } => merr(args[idx], f!("{error}")),
        })
    }
}
