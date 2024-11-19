use super::{location::RefLocationProvider, LocationProvider};

#[derive(Debug, Clone, Copy)]
pub struct Anywhere<'a>(&'a (dyn RefLocationProvider + Sync + Send));

impl<'a> LocationProvider for Anywhere<'a> {
    fn provide(self) -> super::Location {
        self.0.provide()
    }
}
