#[cfg(feature = "sync")]
use std::any::Any;
use std::borrow::Cow;
use std::fmt::Debug;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::Arc;

use egg::{Analysis, Id, Language};

use crate::{Dependancy, Program, Rule};

#[cfg(not(feature = "sync"))]
pub struct DRule<L: Language, N: Analysis<L>>(Rc<dyn DynRule<L, N, Self>>);

#[cfg(feature = "sync")]
pub struct DRule<L: Language, N: Analysis<L>>(Arc<dyn DynRule<L, N, Self>>);

trait DynRule<L: Language, N: Analysis<L>, R>: Any + Rule<L, N, R> {}

impl<L: Language, N: Analysis<L>, R, U: Any + Rule<L, N, R>> DynRule<L, N, R> for U {}

impl<L: Language, N: Analysis<L>> Rule<L, N, Self> for DRule<L, N> {
    fn search(&self, prgm: &mut Program<L, N, Self>, goal: Id) -> Dependancy {
        self.0.search(prgm, goal)
    }

    fn rebuild(&self, prgm: &Program<L, N, Self>) {
        self.0.rebuild(prgm);
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        self.0.debug(f)
    }

    fn name(&self) -> Cow<'_, str> {
        self.0.name()
    }
}

impl<L: Language, N: Analysis<L>> Clone for DRule<L, N> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<L: Language, N: Analysis<L>> Debug for DRule<L, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("DRule").field(&self.0.name()).finish()
    }
}

impl<L: Language, N: Analysis<L>> DRule<L, N> {
    pub fn new<T: Rule<L, N, Self> + Any>(value: T) -> Self {
        Self(Box::<dyn DynRule<L, N, Self>>::from(Box::new(value)).into())
    }
}
