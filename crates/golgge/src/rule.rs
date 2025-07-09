use std::{fmt::Debug, rc::Rc};

use crate::Program;
use egg::{Analysis, Id, Language, RecExpr};

/// Basic prolog-like rules
mod prolog;
pub use prolog::{PrologRule, parser::PlOrRw};

// /// Calls vampire on a goal
// mod vampire;
// pub use vampire::VampireRule;

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash, Clone, Default)]
pub struct Dependancy {
    inner: Vec<Vec<Id>>,
    cut: bool,
}

impl Dependancy {
    pub fn new(inner: Vec<Vec<Id>>) -> Self {
        Self { inner, cut: false }
    }

    pub fn inner(&self) -> &Vec<Vec<Id>> {
        &self.inner
    }

    pub fn cut(&self) -> bool {
        self.cut
    }

    pub fn set_cut(self, cut: bool) -> Self {
        Self { cut, ..self }
    }

    pub fn do_cut(self) -> Self {
        self.set_cut(true)
    }

    pub fn do_not_cut(self) -> Self {
        self.set_cut(false)
    }

    pub fn impossible() -> Self {
        Dependancy {
            inner: vec![],
            cut: false,
        }
    }

    pub fn axiom() -> Self {
        Dependancy {
            inner: vec![vec![]],
            cut: false,
        }
    }
}

pub trait Rule<L: Language, N: Analysis<L>> {
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy;

    fn rebuild(&self, _prgm: &Program<L, N>) {}

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        Ok(())
    }

    fn into_rc(self) -> Rc<dyn Rule<L, N>>
    where
        Self: Sized + 'static,
    {
        Box::<dyn Rule<_, _>>::from(Box::new(self)).into()
    }
}

pub trait Fresh: Sized {
    fn mk_fresh() -> RecExpr<Self>;
}

pub struct DebugRule<'a, L, N>(&'a dyn Rule<L, N>);

impl<'a, L, N> DebugRule<'a, L, N> {
    pub fn new(inner: &'a dyn Rule<L, N>) -> Self {
        Self(inner)
    }
}

impl<'a, L: Language, N: Analysis<L>> Debug for DebugRule<'a, L, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.debug(f)
    }
}

impl<I> FromIterator<I> for Dependancy
where
    I: IntoIterator<Item = Id>,
{
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        Dependancy::new(iter.into_iter().map(|i| i.into_iter().collect()).collect())
    }
}
