use std::backtrace::Backtrace;

use super::{BaseError};

#[non_exhaustive]
#[derive(Debug)]
pub struct InnerError<L> {
    pub location: L,
    pub error: BaseError,
    pub backtrace: Option<std::backtrace::Backtrace>,
}

impl<L> InnerError<L> {
    pub fn new(location: L, error: BaseError) -> Self {
        let backtrace = Backtrace::capture();
        let backtrace = match backtrace.status() {
            std::backtrace::BacktraceStatus::Captured => Some(backtrace),
            _ => None,
        };
        Self {
            location,
            error,
            backtrace,
        }
    }

    pub fn set_location<L2>(self, location:L2) -> InnerError<L2> {
        let Self {  error, backtrace, .. } = self;
        InnerError { location, error , backtrace }
    }
}
