use std::backtrace::Backtrace;

use super::{BaseError, Location};

#[non_exhaustive]
#[derive(Debug)]
pub struct InnerError {
    pub location: Location,
    pub error: BaseError,
    pub backtrace: Option<std::backtrace::Backtrace>,
}

impl InnerError {
    pub fn new(location: Location, error: BaseError) -> Self {
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
