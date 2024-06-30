use std::ops::Deref;

#[derive(Hash, Clone, Copy, PartialEq, Eq, Debug)]
pub struct Guard<T>(T);

impl<T> Deref for Guard<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> From<T> for Guard<T> {
    fn from(value: T) -> Self {
        Guard(value)
    }
}
