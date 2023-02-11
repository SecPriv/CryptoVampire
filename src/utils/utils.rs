use std::ops::{Deref, DerefMut};

#[inline(always)]
pub fn replace_if_eq<T: Eq>(a: T, b: T, c: T) -> T {
    if a == b {
        c
    } else {
        a
    }
}

pub fn clone_iter<'a, E, I>(iter: I) -> impl Iterator<Item = E> + 'a
where
    E: Clone + 'a,
    I: Iterator<Item = &'a E> + 'a,
{
    iter.map(|e| e.clone())
}


pub struct StackBox<T>(T);

impl<T> StackBox<T> {
    pub fn new(t:T) -> Self {
        StackBox(t)
    }
}

impl<T> Deref for StackBox<T> {
    type Target=T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for StackBox<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}