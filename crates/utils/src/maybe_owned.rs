use std::borrow::Borrow;
use std::ops::Deref;

#[derive(Debug, Hash, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MOw<'a, T> {
    Owned(T),
    Borrowed(&'a T),
}

impl<'a, T> Deref for MOw<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        match self {
            MOw::Owned(o) => o,
            MOw::Borrowed(b) => b,
        }
    }
}

impl<'a, T> Borrow<T> for MOw<'a, T> {
    fn borrow(&self) -> &T {
        self.deref()
    }
}
