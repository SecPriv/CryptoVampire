use std::{
    fmt::{Debug, Display},
    hash::Hash,
};
mod location;
pub use location::{Location, RefLocation};

mod location_helper;
pub use location_helper::LocationHelper;

mod empty;

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
pub trait LocationProvider: Debug {
    fn provide(self) -> Location;
}

pub trait LocateHelper : Debug {
    fn help_provide(&self, str:&dyn std::fmt::Display) -> Location;
}


// =========================================================
// ==================== Ref versions =======================
// =========================================================

/// Location provider on refs
pub trait RefLocationProvider: Debug {
    fn provide(&self) -> Location;
}

impl<'a, U> RefLocationProvider for U
where
    &'a U: LocationProvider + 'a,
    U: std::fmt::Debug,
{
    fn provide(&self) -> Location {
        self.provide()
    }
}