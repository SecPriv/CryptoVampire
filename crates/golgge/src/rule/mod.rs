use std::any::Any;
use std::borrow::Cow;
use std::fmt::{Debug, Display};
use std::rc::Rc;

use egg::{Analysis, Id, Language, RecExpr};

use crate::program::Rebuildable;
use crate::proof::Payload;
pub use crate::rule::dynamic::DRule;
use crate::{Program, canonicalize_id_mut};

/// Basic prolog-like rules
mod prolog;
pub use prolog::PrologRule;
pub use prolog::parser::PlOrRw;

mod dynamic;
// mod general;

// /// Calls vampire on a goal
// mod vampire;
// pub use vampire::VampireRule;

/// Represents the dependencies of a rule application.
#[derive(Default)]
#[non_exhaustive]
pub struct Dependancy {
    pub inner: Vec<Vec<Id>>,
    pub cut: bool,
    pub payload: Option<Payload>,
}

impl Dependancy {
    /// Creates a new `Dependancy` with the given inner dependencies.
    pub fn new(inner: Vec<Vec<Id>>) -> Self {
        Self {
            inner,
            cut: false,
            payload: None,
        }
    }

    /// Returns a reference to the inner dependencies.
    pub fn inner(&self) -> &Vec<Vec<Id>> {
        &self.inner
    }

    /// Returns `true` if the rule application should cut the search.
    pub fn cut(&self) -> bool {
        self.cut
    }

    /// Sets whether the rule application should cut the search.
    pub fn set_cut(self, cut: bool) -> Self {
        Self { cut, ..self }
    }

    /// Returns a new `Dependancy` with `cut` set to `true`.
    pub fn do_cut(self) -> Self {
        self.set_cut(true)
    }

    /// Returns a new `Dependancy` with `cut` set to `false`.
    pub fn do_not_cut(self) -> Self {
        self.set_cut(false)
    }

    /// Returns a `Dependancy` representing an impossible proof.
    pub fn impossible() -> Self {
        Dependancy {
            inner: vec![],
            cut: false,
            payload: None,
        }
    }

    /// Returns a `Dependancy` representing an axiom (a proof with no dependencies).
    pub fn axiom() -> Self {
        Dependancy {
            inner: vec![vec![]],
            cut: false,
            payload: None,
        }
    }

    /// Returns `true` if the dependancy represents an impossible proof.
    pub const fn is_impossible(&self) -> bool {
        self.inner.is_empty()
    }

    /// Returns `true` if the dependancy represents an axiom.
    pub fn is_axioms(&self) -> bool {
        self.inner.first().is_some_and(|dep| dep.is_empty())
    }
}

/// A trait for defining rules that can be applied to an e-graph.
pub trait Rule<L: Language, N: Analysis<L>, R> {
    /// Searches for matches of the rule in the e-graph and returns the dependencies.
    fn search(&self, prgm: &mut Program<L, N, R>, goal: Id) -> Dependancy;

    /// Called when the e-graph is rebuilt.
    fn rebuild(&self, _prgm: &Program<L, N, R>) {}

    /// Debugs the rule.
    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<{}>.", self.name())
    }

    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("unamed rule")
    }
}

// /// Converts the rule into an `Rc<dyn Rule<L, N>>`.
// fn into_rc(self) -> Rc<dyn Rule<L, N>>
// where
//     Self: Sized + 'static,
// {
//     Box::<dyn Rule<_, _>>::from(Box::new(self)).into()
// }

/// A trait for types that can generate fresh expressions.
pub trait Fresh: Sized {
    /// Creates a fresh expression.
    fn mk_fresh() -> RecExpr<Self>;
}

// /// A wrapper for `dyn Rule` that implements `Debug`.
// pub struct DebugRule<'a, L, N>(&'a dyn Rule<L, N>);

// impl<'a, L, N> DebugRule<'a, L, N> {
//     /// Creates a new `DebugRule`.
//     pub fn new(inner: &'a dyn Rule<L, N>) -> Self {
//         Self(inner)
//     }
// }

// impl<'a, L: Language, N: Analysis<L>> Debug for DebugRule<'a, L, N> {
//     /// Formats the `DebugRule` for debugging.
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         self.0.debug(f)
//     }
// }

impl<I> FromIterator<I> for Dependancy
where
    I: IntoIterator<Item = Id>,
{
    /// Creates a `Dependancy` from an iterator of iterators of `Id`s.
    fn from_iter<T: IntoIterator<Item = I>>(iter: T) -> Self {
        Dependancy::new(iter.into_iter().map(|i| i.into_iter().collect()).collect())
    }
}
