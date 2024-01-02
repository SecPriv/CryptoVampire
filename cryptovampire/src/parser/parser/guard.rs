use std::ops::Deref;

use cryptovampire_lib::{
    formula::function::Function,
    problem::{cell::MemoryCell, step::Step},
};

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

pub type GuardedFunction<'bump> = Guard<Function<'bump>>;
pub type GuardedStep<'bump> = Guard<Step<'bump>>;
pub type GuardedMemoryCell<'bump> = Guard<MemoryCell<'bump>>;
