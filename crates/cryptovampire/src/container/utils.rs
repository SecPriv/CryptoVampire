use std::cell::Ref;
use std::iter::Map;
use std::slice::Iter;

use super::ScopedContainer;
use crate::formula::function::Function;

/// from <https://stackoverflow.com/a/33542412/10875409>
#[derive(Debug)]
pub struct VecRefWrapperMap<'a, T: 'a, U, F>
where
    F: Fn(&'a T) -> U + Clone,
{
    r: Ref<'a, Vec<T>>,
    f: F,
}

impl<'a, 'b: 'a, T: 'a, U, F> IntoIterator for &'b VecRefWrapperMap<'a, T, U, F>
where
    F: Fn(&'a T) -> U + Clone,
{
    type IntoIter = Map<Iter<'a, T>, F>;
    type Item = U;

    fn into_iter(self) -> Self::IntoIter {
        self.r.iter().map(self.f.clone())
    }
}

pub trait NameFinder<T> {
    fn find_free_name(&self, name: &str) -> String;
}

impl<'bump> NameFinder<Function<'bump>> for ScopedContainer<'bump> {
    fn find_free_name(&self, name: &str) -> String {
        self.find_free_function_name(name)
    }
}

// pub(crate) trait FromNN<'bump>: Sized {
//     type Inner;
//     /// inner lives 'bump
//     unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self;
// }
