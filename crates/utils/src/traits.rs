use std::error::Error;
use std::fmt::Display;

use super::string_ref::StrRef;

pub trait Named {
    fn name(&self) -> &str;
}

pub trait RefNamed<'str> {
    fn name_ref(&self) -> StrRef<'str>;
}

pub trait MyWriteTo {
    fn write_to_fmt<U: std::fmt::Write>(&self, f: &mut U) -> std::fmt::Result;
    fn write_to_io<U: std::io::Write>(&self, f: &mut U) -> std::io::Result<()>;
}

impl<T> MyWriteTo for T
where
    T: Display,
{
    fn write_to_fmt<U: std::fmt::Write>(&self, f: &mut U) -> std::fmt::Result {
        write!(f, "{self}")
    }

    fn write_to_io<U: std::io::Write>(&self, f: &mut U) -> std::io::Result<()> {
        write!(f, "{self}")?;
        f.flush()
    }
}

/// While [std::backtrace::Backtrace] is not supported by `thiserror` this leverages
/// rust builtin backtrace by immediatly crashing when reaching an Err(_) instead of
/// passing it along when compiling in debug mode. The hope is that this becomes a
/// no op once in release mode
pub trait NicerError {
    type Out;
    fn unwrap_display(self) -> Self::Out;
    fn expect_display<F, D>(self, msg: F) -> Self::Out
    where
        F: FnOnce() -> D,
        D: Display;
    fn debug_continue(self) -> Self;
    fn debug_continue_msg<F, D>(self, msg: F) -> Self
    where
        F: FnOnce() -> D,
        D: Display;
}

impl<T, E> NicerError for Result<T, E>
where
    E: Error + std::fmt::Display,
{
    type Out = T;

    fn unwrap_display(self) -> Self::Out {
        match self {
            Ok(o) => o,
            Err(err) => panic!("{err}"),
        }
    }

    fn expect_display<F, D>(self, msg: F) -> Self::Out
    where
        F: FnOnce() -> D,
        D: Display,
    {
        match self {
            Ok(o) => o,
            Err(err) => panic!("{}: {err}", msg()),
        }
    }

    fn debug_continue(self) -> Self {
        if cfg!(debug_assertions) {
            Ok(self.unwrap_display())
        } else {
            self
        }
    }

    fn debug_continue_msg<F, D>(self, msg: F) -> Self
    where
        F: FnOnce() -> D,
        D: Display,
    {
        if cfg!(debug_assertions) {
            Ok(self.expect_display(msg))
        } else {
            self
        }
    }
}
