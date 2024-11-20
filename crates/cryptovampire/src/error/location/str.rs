use super::{Locate, LocateHelper, Location};

impl Locate for str {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "error!\n{err}")?;
        writeln!(f, "at: {self}")?;
        if let Some(bcktr) = backtrace {
            writeln!(f, "backtrace:\n{bcktr}")
        } else {
            Ok(())
        }
    }

    fn pseudo_clone(&self) -> super::Location {
        Location::from_boxed_locate(self.into());
    }
}

impl Locate for String {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.as_ref().location_fmt(err, backtrace, f)
    }

    fn pseudo_clone(&self) -> Location {
        Location::from_boxed_locate(self.into_boxed_str());
    }
}

impl LocateHelper for str {
    fn help_provide(&self, str:&dyn std::fmt::Display) -> Location {
        Location::from_boxed_locate(format!("{str}\nat: {self}").into_boxed_str())
    }
}