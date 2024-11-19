use std::{
    fmt::{Debug, Display},
    hash::Hash,
};

pub use pest_location::PestLocation;
mod pest_location;

mod unit_location;

mod str_location;

pub trait Locate: Debug {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result;
    fn to_location(&self) -> Location;
}

pub trait LocationProvider: Debug {
    fn provide(self) -> Location;
}
pub trait RefLocationProvider: Debug {
    fn provide(&self) -> Location;
}

pub trait PreLocation: Debug {
    fn help_provide(&self, extra: &dyn Display) -> Location;
}

#[derive(Debug)]
pub struct Location(Box<dyn Locate + 'static + Sync + Send>);

#[derive(Debug, Clone, Copy)]
pub struct RefLocation<'a>(&'a (dyn Locate + Sync + Send));

impl Location {
    #[inline]
    pub fn from_locate<L>(l: L)
    where
        L: Locate + 'static + Sync + Send + Sized,
    {
        Self(Box::new(l))
    }
}

impl Locate for Location {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.location_fmt(err, backtrace, f)
    }
    
    fn to_location(&self) -> Location {
        self.0.to_location()
    }
}

impl<'a> Locate for RefLocation<'a> {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.location_fmt(err, backtrace, f)
    }
    
    fn to_location(&self) -> Location {
        self.0.to_location()
    }
}

impl<'a, U> RefLocationProvider for U
where
    &'a U: LocationProvider + 'a,
    U: Debug,
{
    fn provide(&self) -> Location {
        self.provide()
    }
}

impl Default for Location {
    fn default() -> Self {
        Location::from_locate(());
    }
}