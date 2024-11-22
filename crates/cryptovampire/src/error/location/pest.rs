use std::fmt::{Display, Write};

use pest::error::ErrorVariant;

use super::{Locate, LocationProvider};

#[derive(Debug, Clone)]
struct SpanLocation {
    str: Box<str>,
    start: usize,
    end: usize,
}

impl Locate for SpanLocation {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let mut message = format!("error: {err}\n");
        if let Some(bktr) = backtrace {
            writeln!(message, "backtrace:\n{bktr}")?;
        }
        let variant: ErrorVariant<crate::parser::Rule> =
            pest::error::ErrorVariant::CustomError { message };
        let span = pest::Span::new(&self.str, self.start, self.end).unwrap();
        let err = pest::error::Error::new_from_span(variant, span);
        err.fmt(f)
    }

    fn pseudo_clone(&self) -> super::Location {
        super::Location::from_locate(self.clone())
    }
}

impl<'str> LocationProvider for pest::Span<'str> {
    fn provide(self) -> super::Location {
        let span_location = SpanLocation {
            str: self.as_str().into(),
            start: self.start(),
            end: self.end(),
        };
        super::Location::from_locate(span_location)
    }
}
