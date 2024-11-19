use super::*;

impl crate::Sealed for () {}
impl Locate for () {
fn location_fmt(
    &self,
    err: &crate::error::BaseError,
    backtrace: Option<&std::backtrace::Backtrace>,
    f: &mut std::fmt::Formatter<'_>,
) -> std::fmt::Result {
        std::fmt::Display::fmt(err, f)?;
        match backtrace {
            Some(bt) => write!(f, "\nbacktrace:\n{}", bt),
            None => Ok(()),
        }
    }
}
// impl LocationProvider<Self> for () {
//     fn provide(self) -> Self {
//         self
//     }
// }
