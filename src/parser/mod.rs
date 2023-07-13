mod ast;
mod parser;
// mod builders;

use pest::error::Error;
use pest_derive::Parser;

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

#[inline(always)]
fn err<E: std::error::Error, T>(err: E) -> Result<T, E> {
    if cfg!(debug_assertions) {
        Err(err).unwrap()
    } else {
        Err(err)
    }
}

macro_rules! merr {
    ($span:expr; $msg:literal $(,$args:expr)*) => {
        Error::new_from_span(
            pest::error::ErrorVariant::CustomError {
                message: format!($msg $(,$args)*),
            },
            $span,
        )
    };
}

pub(crate) use merr;
