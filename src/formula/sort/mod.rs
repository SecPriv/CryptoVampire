pub mod builtins;
// pub mod collection;
pub mod sort_proxy;
pub mod sorted;
use core::fmt::Debug;
use std::{fmt::Display, hash::Hash};

pub mod inner;

use crate::{
    container::{
        allocator::ContainerTools, contained::Containable, reference::Reference, StaticContainer,
    },
    environement::traits::{KnowsRealm, Realm},
    force_lifetime,
    utils::{precise_as_ref::PreciseAsRef, string_ref::StrRef, traits::RefNamed},
};

use self::inner::{Index, Other, TermBase, UserEvaluatable};

pub type Sort<'bump> = Reference<'bump, InnerSort<'bump>>;

impl<'bump> Containable<'bump> for InnerSort<'bump> {}

unsafe impl<'bump> Sync for Sort<'bump> {}
unsafe impl<'bump> Send for Sort<'bump> {}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerSort<'bump> {
    Base(TermBase),
    UserEvaluatable(UserEvaluatable<'bump>),
    Index(Index),
    Other(Other),
}

impl<'bump> InnerSort<'bump> {
    /// Returns `true` if the inner sort is [`UserEvaluatable`].
    ///
    /// [`UserEvaluatable`]: InnerSort::UserEvaluatable
    #[must_use]
    pub fn is_user_evaluatable(&self) -> bool {
        matches!(self, Self::UserEvaluatable(..))
    }

    pub fn as_user_evaluatable(&self) -> Option<&UserEvaluatable<'bump>> {
        if let Self::UserEvaluatable(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the inner sort is [`Index`].
    ///
    /// [`Index`]: InnerSort::Index
    #[must_use]
    pub fn is_index(&self) -> bool {
        matches!(self, Self::Index(..))
    }

    pub fn as_index(&self) -> Option<&Index> {
        if let Self::Index(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the inner sort is [`Base`].
    ///
    /// [`Base`]: InnerSort::Base
    #[must_use]
    pub fn is_base(&self) -> bool {
        matches!(self, Self::Base(..))
    }

    pub fn as_base(&self) -> Option<&TermBase> {
        if let Self::Base(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn name(&self) -> StrRef<'_> {
        self.name_ref()
    }

    pub fn evaluated_sort(&self) -> Option<Sort<'bump>> {
        match self {
            InnerSort::Base(b) => b.evaluated_sort(),
            InnerSort::UserEvaluatable(ue) => ue.evaluated_sort(),
            _ => None,
        }
    }

    pub fn is_evaluated(&self) -> bool {
        match self {
            InnerSort::Base(b) => b.is_evaluated(),
            InnerSort::UserEvaluatable(ue) => ue.is_evaluated(),
            _ => false,
        }
    }

    /// Returns `true` if the inner sort is [`Other`].
    ///
    /// [`Other`]: InnerSort::Other
    #[must_use]
    pub fn is_other(&self) -> bool {
        matches!(self, Self::Other(..))
    }

    pub fn as_other(&self) -> Option<&Other> {
        if let Self::Other(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'a> Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner().name())
    }
}

impl<'a> Sort<'a> {
    // ~~~~~~~~~~~~~~~~~~ is ~~~~~~~~~~~~~~~~~~~~
    pub fn is_term_algebra(&self) -> bool {
        self.as_inner().evaluated_sort().is_some() || self.as_inner().is_other()
    }

    pub fn is_built_in(&self) -> bool {
        self.as_ref().is_base()
    }

    pub fn is_evaluatable(&self) -> bool {
        match self.as_ref() {
            InnerSort::Base(TermBase::Condition)
            | InnerSort::Base(TermBase::Message)
            | InnerSort::UserEvaluatable(UserEvaluatable::Symbolic { .. }) => true,
            _ => false,
        }
    }

    // ~~~~~~~~~~~~~~~ builders ~~~~~~~~~~~~~~~~~
    pub fn new_user<C>(container: &'a C, name: Box<str>) -> (Sort<'a>, Sort<'a>)
    where
        C: ContainerTools<'a, InnerSort<'a>, R<'a> = Self>,
    {
        <C as ContainerTools<'a, (InnerSort<'a>, InnerSort<'a>)>>::alloc_cyclic(
            // C::alloc_cyclic(
            container,
            |(symbolic, eval)| {
                let inner_symbolic =
                    InnerSort::UserEvaluatable(UserEvaluatable::Symbolic { name, eval: *eval });
                let inner_eval = InnerSort::UserEvaluatable(UserEvaluatable::Evaluated {
                    symbolic: *symbolic,
                });
                (inner_symbolic, inner_eval)
            },
        )
        .expect("not never initialized")
    }

    // ~~~~~~~~~~~~~~~~~ cast ~~~~~~~~~~~~~~~~~~~

    fn inner(&self) -> &'a InnerSort<'a> {
        self.precise_as_ref()
    }

    pub fn as_sort<'b>(&self) -> Sort<'b>
    where
        'a: 'b,
    {
        *self
    }

    // ~~~~~~~~~~~~~~~~ other ~~~~~~~~~~~~~~~~~~~
    pub fn name(&self) -> StrRef<'a> {
        self.precise_as_ref().name()
    }

    pub fn evaluated_sort(&self) -> Option<Sort<'a>> {
        self.precise_as_ref().evaluated_sort()
    }

    /// Equality modulo a [Realm]
    ///
    /// ```rust
    /// assert!(BOOL.eq_realm(CONDITION.as_ref(), Realm::Evaluated))
    /// ```
    pub fn eq_realm<R>(&self, other: &Self, realm: &R) -> bool
    where
        R: KnowsRealm,
    {
        (self == other)
            || match realm.get_realm() {
                Realm::Symbolic => false,
                Realm::Evaluated => {
                    self.is_evaluatable() && (self.evaluated_sort() == other.evaluated_sort())
                }
            }
    }

    /// The [Realm] in which this sort should be used. [None] if it doesn't matter or can't be decided
    pub fn realm(&self) -> Option<Realm> {
        match self.as_inner() {
            InnerSort::Base(b) => Some(b.get_realm()),
            InnerSort::UserEvaluatable(ue) => Some(ue.get_realm()),
            _ => None,
        }
    }

    force_lifetime!(Sort, 'a);
}

pub fn new_static_sort(inner: InnerSort<'static>) -> Sort<'static> {
    StaticContainer.alloc_inner(inner)
}

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerSort<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        match self {
            InnerSort::Base(b) => b.name(),
            InnerSort::UserEvaluatable(ue) => ue.name(),
            InnerSort::Index(idx) => idx.name(),
            InnerSort::Other(o) => o.name(),
        }
    }
}
