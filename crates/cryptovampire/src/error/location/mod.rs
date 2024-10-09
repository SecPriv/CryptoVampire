use std::fmt::{Debug, Display};

pub trait Location: crate::Sealed + Sized + Debug {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

pub use pest_location::PestLocation;
mod pest_location;

mod unit_location {
    use super::*;

    impl crate::Sealed for () {}
    impl Location for () {
        fn location_fmt(
            err: &crate::Error<Self>,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            std::fmt::Display::fmt(err.get_error(), f)?;
            match err.get_backtrace() {
                Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
                None => Ok(()),
            }
        }
    }
    // impl LocationProvider<Self> for () {
    //     fn provide(self) -> Self {
    //         self
    //     }
    // }
}

pub use str_location::StrLocation;
mod str_location {
    use super::{Location, LocationProvider};

    #[derive(Debug)]
    pub struct StrLocation(pub Box<str>);
    impl crate::Sealed for StrLocation {}
    impl Location for StrLocation {
        fn location_fmt(
            err: &crate::Error<Self>,
            f: &mut std::fmt::Formatter<'_>,
        ) -> std::fmt::Result {
            writeln!(f, "error at: {}\ndecsciption:", err.get_location().0)?;
            std::fmt::Display::fmt(err.get_error(), f)?;
            match err.get_backtrace() {
                Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
                None => Ok(()),
            }
        }
    }

    // impl LocationProvider<Self> for StrLocation {
    //     fn provide(self) -> Self {
    //         self
    //     }
    // }
}

pub trait PreLocation {
    type L: Location;

    fn help_provide<T>(&self, extra: &T) -> Self::L
    where
        T: Sized + Display;
}

impl<'str> PreLocation for pest::Span<'str> {
    type L = PestLocation;

    fn help_provide<T>(&self, _: &T) -> Self::L
    where
        T: Sized + Display,
    {
        (*self).into()
    }
}

impl PreLocation for () {
    type L = StrLocation;

    fn help_provide<T>(&self, t: &T) -> Self::L
    where
        T: Sized + Display,
    {
        StrLocation(t.to_string().into_boxed_str())
    }
}

pub trait LocationProvider<L: Location> {
    fn provide(self) -> L;
}

impl<L:Location> LocationProvider<L> for L {
    fn provide(self) -> Self {
        self
    }
}

impl<'a> LocationProvider<PestLocation> for pest::Span<'a> {
    fn provide(self) -> PestLocation {
        self.into()
    }
}

impl<'a> LocationProvider<PestLocation> for pest::Position<'a> {
    fn provide(self) -> PestLocation {
        self.into()
    }
}

impl<'a> LocationProvider<StrLocation> for &'a str {
    fn provide(self) -> StrLocation {
        StrLocation(self.into())
    }
}

impl<'a, 'str, R: pest::RuleType> LocationProvider<PestLocation>
    for &'a pest::iterators::Pair<'str, R>
{
    fn provide(self) -> PestLocation {
        self.as_span().into()
    }
}

// impl ProvideLocation<OwnedSpan> for pest::
