use std::fmt::{Debug, Display};
#[allow(clippy::module_inception)]
mod location;
pub use location::Location;

mod location_helper;

use crate::error_at;

mod empty;
mod pest;
mod str;

/// Something that points a "location" in an input file
///
/// The idea is to have a somewhat lose definition of what
/// a "location" is supposed to be, so that we can be as flexible as possible
pub trait Locate: Debug {
    /// Given the error variant and the backtrace (if any)
    /// returns the error message.
    ///
    /// This is what will be printed to the screen
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result;

    /// To make it "clonable"
    fn pseudo_clone(&self) -> Location;
}

/// Something that can give a location
///
/// This trait is useful for triggering errors
pub trait LocationProvider {
    fn provide(self) -> Location;

    fn err_with<D>(self, f: impl FnOnce() -> D) -> crate::Error
    where
        D: Display,
        Self: Sized,
    {
        let str = f();
        error_at!(self, "{str}")
    }
}

impl<F, P> LocationProvider for F
where
    F: FnOnce() -> P,
    P: LocationProvider,
{
    fn provide(self) -> Location {
        self().provide()
    }
}

pub trait LocateHelper: Debug {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> Location;
}

// =========================================================
// ==================== Ref versions =======================
// =========================================================

/// Location provider on refs
pub trait RefLocationProvider: Debug {
    fn provide(&self) -> Location;
}

impl<U> RefLocationProvider for U
where
    for<'a> &'a U: LocationProvider,
    U: std::fmt::Debug,
{
    fn provide(&self) -> Location {
        LocationProvider::provide(self)
    }
}
