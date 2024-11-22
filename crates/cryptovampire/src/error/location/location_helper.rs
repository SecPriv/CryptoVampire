use super::LocateHelper;

#[derive(Debug, Copy, Clone)]
pub struct LocationHelper<'a>(&'a (dyn LocateHelper + Sync + Send));

impl<'a> LocateHelper for LocationHelper<'a> {
    fn help_provide(&self, str: &dyn std::fmt::Display) -> super::Location {
        self.0.help_provide(str)
    }
}
