use super::Locate;

#[derive(Debug, Copy, Clone, Eq, Ord, PartialEq, PartialOrd)]
pub struct NoLocation;

impl Locate for NoLocation {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        
    }

    fn pseudo_clone(&self) -> super::Location {
        todo!()
    }
}