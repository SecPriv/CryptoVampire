use std::fmt::{Debug, Display};

pub trait Location: crate::Sealed + Sized + Debug {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result;
}

#[derive(Debug)]
pub struct OwnedSpan {
    input: Box<str>,
    start: usize,
    end: usize,
}

impl<'a> From<pest::Span<'a>> for OwnedSpan {
    fn from(value: pest::Span<'a>) -> Self {
        Self {
            input: value.get_input().into(),
            start: value.start(),
            end: value.end(),
        }
    }
}

impl OwnedSpan {
    pub fn as_span<'a>(&'a self) -> pest::Span<'a> {
        pest::Span::new(&self.input, self.start, self.end).expect("could not convert to span")
    }
}

impl crate::Sealed for OwnedSpan {}

impl Location for OwnedSpan {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let span = err.get_location().as_span();
        let pest_error = match err.get_error() {
            crate::BaseError::PestErrorVariant(variant) => {
                &pest::error::Error::new_from_span(variant.clone(), span)
            }
            crate::BaseError::PestError(e) => e,
            e => {
                let variant = pest::error::ErrorVariant::<crate::parser::Rule>::CustomError {
                    message: e.to_string(),
                };
                &pest::error::Error::new_from_span(variant, span)
            }
        };
        std::fmt::Display::fmt(pest_error, f)?;
        match err.get_backtrace() {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

impl crate::Sealed for () {}
impl Location for () {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(err.get_error(), f)?;
        match err.get_backtrace() {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

#[derive(Debug)]
pub struct StrLocation(Box<str>);
impl crate::Sealed for StrLocation {}
impl Location for StrLocation {
    fn location_fmt(err: &crate::Error<Self>, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "error at: {}\ndecsciption:", err.get_location().0)?;
        std::fmt::Display::fmt(err.get_error(), f)?;
        match err.get_backtrace() {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

pub type SelfLocation<T> = <<T as HasLocation>::PreL as WithHasLocation>::L;

pub trait HasLocation: Display + Sized {
    type PreL: WithHasLocation;

    fn get_pre_location(&self) -> &Self::PreL;

    fn get_location(&self) -> SelfLocation<Self> {
        let pl = self.get_pre_location();
        pl.produce_location(self)
    }
}

pub trait WithHasLocation {
    type L: Location;

    fn produce_location<T>(&self, t: &T) -> Self::L
    where
        T: HasLocation<PreL = Self> + Display;
}

impl<'a> WithHasLocation for pest::Span<'a> {
    type L = OwnedSpan;

    fn produce_location<T>(&self, _: &T) -> OwnedSpan
    where
        T: HasLocation<PreL = Self> + Display,
    {
        OwnedSpan::from(*self)
    }
}

impl<'a> WithHasLocation for () {
    type L = StrLocation;

    fn produce_location<T>(&self, t: &T) -> StrLocation
    where
        T: HasLocation<PreL = Self> + Display,
    {
        StrLocation(t.to_string().into_boxed_str())
    }
}
