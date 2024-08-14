pub mod ast;
mod parser;
// mod builders;

use ast::INIT_STEP_AST;
pub(crate) use parser::parse_str;
use static_init::dynamic;

use std::borrow::Borrow;

use pest_derive::Parser;

pub const USED_KEYWORDS: &'static [&'static str] = &[
    "and",
    "or",
    "not",
    "ite",
    "assert",
    "assert-not",
    "assert-theory",
    "rewrite",
    "subterm",
    "True",
    "False",
    "true",
    "false",
    "implies",
    "forall",
    "exists",
    "match",
    "declare-datatype",
    "declare-fun",
    "declare-sort",
    "define-fun",
    "define-fun-rec",
    "define-sort",
    "Int",
    "Real",
    "Array",
];

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

pub type MResult<T> = std::result::Result<T, error::InputError>;

// #[inline(always)]
// /// imediadly crashes in debug mode (to get the stacktrace and everything)
// /// it properly bubles up the error in release mode
// fn err<E: std::error::Error, T>(err: E) -> Result<T>
// where
//     error::InputError: From<E>,
// {
//     if cfg!(debug_assertions) {
//         Err(err).unwrap_display()?
//     } else {
//         Err(err)?
//     }
// }

// fn merr<'a>(s: Span<'a>, msg: String) -> error::InputError {
//     pest::error::Error::new_from_span(pest::error::ErrorVariant::CustomError { message: msg }, s)
//         .into()
// }

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

macro_rules! lerr {
    ($loc:expr, $($arg:tt)*) => {
        $loc.err_with(|| std::fmt::format!($($arg:tt)*))
    };
}

macro_rules! lbail {
    ($loc:expr, $($arg:tt)*) => {
        utils::traits::NicerError::debug_continue(lerr!($loc, $($arg:tt)*))?
    };
}

use utils::{string_ref::StrRef, traits::NicerError};

// trait IntoRuleResult<T, Err> {
//     fn into_rr<'a>(self, span: Span<'a>) -> Result<T>;
// }

// impl<'bump, T> IntoRuleResult<T, InferenceError<'bump>>
//     for std::result::Result<T, InferenceError<'bump>>
// {
//     fn into_rr<'a>(self, span: Span<'a>) -> Result<T> {
//         match self {
//             Ok(x) => Ok(x),
//             Err(e) => err(merr(span, f!("{}", e))),
//         }
//     }
// }

// trait IntoRuleResultFunction<T, Err> {
//     fn into_rr<'a, I>(self, fun: Span<'a>, args: I) -> Result<T>
//     where
//         I: Index<usize, Output = Span<'a>>;
// }

// impl<'bump, T> IntoRuleResultFunction<T, CheckError<'bump>>
//     for std::result::Result<T, CheckError<'bump>>
// {
//     fn into_rr<'a, I>(self, fun: Span<'a>, args: I) -> Result<T>
//     where
//         I: Index<usize, Output = Span<'a>>,
//     {
//         self.map_err(|err| match err {
//             CheckError::WrongNumberOfArguments { got, expected } => merr(
//                 fun,
//                 format!("wring number of arguments: expected {expected:?}, got {got}"),
//             ),
//             CheckError::SortError {
//                 position: None,
//                 error,
//             } => merr(fun, f!("{error}")),
//             CheckError::SortError {
//                 position: Some(idx),
//                 error,
//             } => merr(args[idx], f!("{error}")),
//         })
//     }
// }

mod error {

    use std::backtrace;
    use std::fmt::Display;

    use anyhow::anyhow;
    use pest::iterators::Pair;
    use pest::Span;
    use thiserror::Error;
    use utils::implvec;
    use utils::iter_array;

    use super::MResult;
    use super::Rule;

    #[derive(Error, Debug)]
    pub enum InputError {
        #[error("localised error:\n{pest}\n{err:}")]
        OtherPestError {
            pest: Box<pest::error::Error<Rule>>,
            #[source]
            err: anyhow::Error,
        },

        #[error("No location:\n{0}")]
        Other(#[source] anyhow::Error),
    }

    impl InputError {
        pub fn new_with_location<'a>(location: &Location<'a>, err: anyhow::Error) -> Self {
            match &location.0 {
                InnerLocation::Span(s) => {
                    use pest::error::*;
                    InputError::OtherPestError {
                        pest: Box::new(Error::new_from_span(
                            ErrorVariant::CustomError { message: "".into() },
                            s.clone(),
                        )),
                        err: err.into(),
                    }
                }
                InnerLocation::None => InputError::Other(err.into()),
            }
        }

        pub fn new_with_pest(pest: pest::error::Error<Rule>, err: anyhow::Error) -> Self {
            Self::OtherPestError {
                pest: Box::new(pest),
                err,
            }
        }

    }

    #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Default)]
    pub struct Location<'a>(InnerLocation<'a>);

    #[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Default)]
    enum InnerLocation<'a> {
        Span(Span<'a>),
        #[default]
        None,
    }

    impl<'a> From<Span<'a>> for Location<'a> {
        fn from(value: Span<'a>) -> Self {
            Location(InnerLocation::Span(value))
        }
    }
    impl<'a, 'b> From<&'b Span<'a>> for Location<'a> {
        fn from(value: &'b Span<'a>) -> Self {
            Location(InnerLocation::Span(*value))
        }
    }

    impl<'a, 'b> From<&'b Self> for Location<'a> {
        fn from(value: &'b Self) -> Self {
            value.clone()
        }
    }

    impl<'a, 'b> From<&'b Pair<'a, Rule>> for Location<'a> {
        fn from(value: &'b Pair<'a, Rule>) -> Self {
            value.as_span().into()
        }
    }

    impl<'a> Location<'a> {
        pub fn err_with<S>(&self, f: impl FnOnce() -> S) -> InputError
        where
            S: Display,
        {
            InputError::new_with_location(self, anyhow!("{:}", f()))
        }

        pub fn bail_with<T, S>(&self, f: impl FnOnce() -> S) -> super::MResult<T>
        where
            S: Display,
        {
            Err(anyhow!("{:}", f())).with_location(self)
        }

        pub fn wrong_rule<T>(
            &self,
            positive: implvec!(Rule),
            negatives: implvec!(Rule),
        ) -> super::MResult<T> {
            let positives = positive.into_iter().collect();
            let negatives = negatives.into_iter().collect();
            let e = pest::error::ErrorVariant::ParsingError {
                positives,
                negatives,
            };
            Err(match &self.0 {
                InnerLocation::Span(span) => InputError::new_with_pest(
                    pest::error::Error::new_from_span(e, *span),
                    anyhow!(""),
                ),
                InnerLocation::None => InputError::Other(e.into()),
            })
        }

        pub fn none() -> Self {
            Self(InnerLocation::None)
        }
    }

    pub trait WithLocation<T> {
        fn with_location<'a, I>(self, location: I) -> MResult<T>
        where
            Location<'a>: From<I>;
    }

    impl<T, E> WithLocation<T> for std::result::Result<T, E>
    where
        anyhow::Error: From<E>,
    {
        fn with_location<'a, I>(self, location: I) -> MResult<T>
        where
            Location<'a>: From<I>,
        {
            self.map_err(|err| InputError::new_with_location(&location.into(), err.into()))
        }
    }
    impl<T> WithLocation<T> for Option<T>
    {
        fn with_location<'a, I>(self, location: I) -> MResult<T>
        where
            Location<'a>: From<I>,
        {
            self.ok_or_else(|| InputError::new_with_location(&location.into(), anyhow!("None")))
        }
    }

    impl From<pest::error::Error<Rule>> for InputError {
        fn from(value: pest::error::Error<Rule>) -> Self {
            Self::OtherPestError {
                pest: Box::new(value),
                err: anyhow!(""),
            }
        }
    }

    macro_rules! err_from {
        ($t:ty) => {
            impl From<$t> for InputError
            where
                anyhow::Error: From<$t>,
            {
                fn from(value: $t) -> Self {
                    Self::Other(value.into())
                }
            }
        };
    }

    err_from!(anyhow::Error);
    err_from!(iter_array::WrongLengthError);
    err_from!(iter_array::NotEnoughItemError);

    #[macro_export]
    macro_rules! err_at {
        ($location:expr, $($args:tt)*) => {
            $crate::parser::InputError::new_with_location($location, anyhow::anyhow!($($args)*))
            // $crate::parser::Location::from($location).err_with(|| f!($($args)*))
        };
        (@ $($args:tt)*) => {
            $crate::err_at!(&$crate::parser::Location::default(), $($args)* )
        };
    }

    #[macro_export]
    macro_rules! bail_at {
        ($location:expr, $($args:tt)*) => {
            $crate::parser::Location::from($location).bail_with(|| utils::f!($($args)*))?
        };
        (@ $($args:tt)*) => {
            $crate::parser::Location::from($crate::parser::Location::default()).bail_with(|| utils::f!($($args)*))?
        };
    }
}
pub use error::{InputError, Location, WithLocation};

pub trait HasInitStep: Sized {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'a, Self>;
    // fn from_static(s:&'static str) -> Self;
}

pub trait FromStaticString {
    fn from_static(s: &'static str) -> Self;
}

#[dynamic]
static INIT_STEP_AST_STR: ast::Step<'static, &'static str> = INIT_STEP_AST();

#[dynamic]
static INIT_STEP_AST_STRREF: ast::Step<'static, StrRef<'static>> = INIT_STEP_AST();

impl<'str> HasInitStep for &'str str {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'a, Self> {
        &INIT_STEP_AST_STR
    }
}

impl<'str> FromStaticString for &'str str {
    fn from_static(s: &'static str) -> Self {
        s
    }
}

impl<'str> HasInitStep for StrRef<'str> {
    fn ref_init_step_ast<'a>() -> &'a ast::Step<'a, Self> {
        &INIT_STEP_AST_STRREF
    }
}

impl<'str> FromStaticString for StrRef<'str> {
    fn from_static(s: &'static str) -> Self {
        s.into()
    }
}

pub trait Pstr:
    Borrow<str>
    + std::hash::Hash
    + Clone
    + std::fmt::Display
    + Eq
    // + From<&'static str>
    + std::fmt::Debug
    + HasInitStep
    + FromStaticString
{
    fn as_str(&self) -> &str {
        self.borrow()
    }
}
impl<T> Pstr for T where
    T: Borrow<str>
        + std::hash::Hash
        + Clone
        + std::fmt::Display
        + Eq
        // + From<&'static str>
        + std::fmt::Debug
        + HasInitStep
        + FromStaticString
{
}
