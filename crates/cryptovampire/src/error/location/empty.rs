use super::{Locate, LocateHelper, Location, LocationProvider};

impl Locate for () {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(f, "error!\n{err}")?;
        if let Some(bcktr) = backtrace {
            writeln!(f, "backtrace:\n{bcktr}")
        } else {
            Ok(())
        }
    }

    fn pseudo_clone(&self) -> Location {
        self.provide()
    }
}

impl<'a> LocationProvider for &'a () {
    fn provide(self) -> Location {
        Location::from_locate(())
    }
}

impl LocationProvider for () {
    fn provide(self) -> Location {
        (&()).provide()
    }
}

impl LocateHelper for () {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> Location {
        Location::from_display(str)
    }
}
