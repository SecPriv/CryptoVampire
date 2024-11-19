use super::{Locate, LocationProvider};

impl Locate for str {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "error at: {}\ndecsciption:", self)?;
        std::fmt::Display::fmt(err, f)?;
        match backtrace {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}

impl<'a> Locate for &'a str {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        str::location_fmt(*self, err, backtrace, f)
    }
}