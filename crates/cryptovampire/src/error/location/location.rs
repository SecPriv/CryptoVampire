use super::{Locate, LocationProvider, RefLocationProvider};

/// This is the main struct to use with [Locate]. We use dynamic dispatch
#[derive(Debug)]
pub struct Location(Box<dyn Locate + 'static + Sync + Send>);

impl Location {
    #[inline]
    pub fn from_locate<L>(l: L)
    where
        L: Locate + 'static + Sync + Send + Sized,
    {
        Self::from_boxed_locate(Box::new(l))
    }
    
    #[inline]
    pub fn from_boxed_locate<L>(l: Box<L>)
    where
        L: Locate + 'static + Sync + Send ,
    {
        Self(l)
    }
}

impl Locate for Location {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.location_fmt(err, backtrace, f)
    }

    fn pseudo_clone(&self) -> Location {
        self.0.pseudo_clone()
    }
}

impl LocationProvider for Location {
    fn provide(self) -> Location {
        self
    }
}

/// Same as [Location] but without owning the data
///
/// This has the advantage of implementing [Clone] and [Copy]
/// but it must be turned into a [Location] when triggering an error
/// and possibly when we want to lose the lifetime information.
#[derive(Debug, Clone, Copy)]
pub struct RefLocation<'a>(&'a (dyn Locate + Sync + Send));

impl<'a> RefLocation<'a> {
    #[inline]
    pub fn from_location<L>(l: &'a L)
    where
        L: Locate + Sync + Send,
    {
        Self(l)
    }
}

impl<'a> Locate for RefLocation<'a> {
    fn location_fmt(
        &self,
        err: &crate::error::BaseError,
        backtrace: Option<&std::backtrace::Backtrace>,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.0.location_fmt(err, backtrace, f)
    }

    fn pseudo_clone(&self) -> Location {
        self.0.pseudo_clone()
    }
}
