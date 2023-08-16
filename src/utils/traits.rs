use std::{error::Error, fmt::Display};

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
        write!(f, "{self}")
    }
}

pub trait NicerError {
    type Out;
    fn unwrap_display(self) -> Self::Out;
    fn expect_display(self, msg: &str) -> Self::Out;
    fn debug_continue(self) -> Self;
    fn debug_continue_msg(self, msg:&str) -> Self;
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

    fn expect_display(self, msg: &str) -> Self::Out {
        match self {
            Ok(o) => o,
            Err(err) => panic!("{msg}: {err}"),
        }
    }

    fn debug_continue(self) -> Self {
        if cfg!(debug_assertions) {
            Ok(self.unwrap_display())
        } else {
            self
        }
    }

    fn debug_continue_msg(self, msg:&str) -> Self {
        if cfg!(debug_assertions) {
            Ok(self.expect_display(msg))
        } else {
            self
        }
    }
}
