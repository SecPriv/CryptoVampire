use std::ops::Deref;

use utils::precise_as_ref::PreciseAsRef;

use super::{Function, InnerFunction};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Dispacher<'a, T> {
    inner: &'a T,
    function: Function<'a>,
}

impl<'a, T> Deref for Dispacher<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.inner
    }
}

impl<'a> From<Function<'a>> for Dispacher<'a, InnerFunction<'a>> {
    fn from(value: Function<'a>) -> Self {
        Dispacher {
            inner: value.precise_as_ref(),
            function: value,
        }
    }
}

impl<'a, T> Dispacher<'a, T> {
    pub fn function(&self) -> Function<'a> {
        self.function
    }

    pub fn back_to_top(self) -> Dispacher<'a, InnerFunction<'a>> {
        self.function.into()
    }

    pub fn map<U>(self, f: impl FnOnce(&'a T) -> &'a U) -> Dispacher<'a, U> {
        Dispacher {
            inner: f(self.inner),
            function: self.function,
        }
    }
}
