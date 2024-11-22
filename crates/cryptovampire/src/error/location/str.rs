use utils::string_ref::StrRef;

use super::{Locate, LocateHelper, Location, LocationProvider};

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
        let str = String::from(self);
        Location::from_locate(str)
    }
}

impl Locate for String {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let str: &str = self.as_ref();
        str.location_fmt(err, backtrace, f)
    }

    fn pseudo_clone(&self) -> Location {
        Location::from_locate(self.clone())
    }
}

impl LocateHelper for str {
    fn help_provide(&self, str: &(dyn std::fmt::Display)) -> Location {
        Location::from_locate(format!("{str}\nat: {self}"))
    }
}

impl<'a, 'b> LocationProvider for &'b StrRef<'a> {
    fn provide(self) -> Location {
        Location::from_locate(self.to_string())
    }
}
