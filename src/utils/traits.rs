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
    fn write_to_io<U: std::io::Write>(&self, f:&mut U) -> std::io::Result<()>;
}

impl<T> MyWriteTo for T where T:Display {
    fn write_to_fmt<U: std::fmt::Write>(&self, f: &mut U) -> std::fmt::Result {
        write!(f, "{self}")
    }

    fn write_to_io<U: std::io::Write>(&self, f:&mut U) -> std::io::Result<()> {
        write!(f, "{self}")
    }
}