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
}
