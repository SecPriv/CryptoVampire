pub mod builtins;
// pub mod collection;
pub mod sort_proxy;
pub mod sorted;
use bitflags::bitflags;
use core::fmt::Debug;
use std::{fmt::Display, hash::Hash};

pub mod inner;

use crate::{
    container::{
        allocator::ContainerTools, contained::Containable, reference::Reference, ScopedContainer,
        StaticContainer,
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

// impl<'a> Ord for Sort<'a> {
//     fn cmp(&self, other: &Self) -> std::cmp::Ordering {
//         // Ord::cmp(&Rc::as_ptr(&self.0), &Rc::as_ptr(&other.0))
//         if self != other {
//             Ord::cmp(self.name(), other.name())
//                 .then(Ord::cmp(&self.as_ptr_usize(), &self.as_ptr_usize()))
//         } else {
//             Ordering::Equal
//         }
//     }
// }

// impl<'a> PartialOrd for Sort<'a> {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         Some(self.cmp(&other))
//     }
// }

impl<'a> Display for Sort<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner().name())
    }
}

// impl<'a> Hash for Sort<'a> {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         self.as_ptr_usize().hash(state);
//     }
// }

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

// impl<'bump> AsRef<HiddenSort<'bump>> for InnerSort<'bump> {
//     fn as_ref(&self) -> &HiddenSort<'bump> {
//         &self.inner
//     }
// }

// impl<'bump> Reference<'bump> for Sort<'bump> {
//     type Inner<'a> = InnerSort<'a> where 'a:'bump;

//     fn from_ref(ptr: &'bump Option<InnerSort<'bump>>) -> Self {
//         Self {
//             inner: NonNull::from(ptr),
//             container: Default::default(),
//         }
//     }

//     fn to_ref(&self) -> &'bump Option<Self::Inner<'bump>> {
//         unsafe { self.inner.as_ref() }
//     }
// }

// impl<'bump> PreciseAsRef<'bump, InnerSort<'bump>> for Sort<'bump> {
//     fn precise_as_ref(&self) -> &'bump InnerSort<'bump> {
//         unsafe { self.inner.as_ref() } // for self to exists, container must exists
//     }
// }

// impl<'bump> AsRef<InnerSort<'bump>> for Sort<'bump> {
//     fn as_ref(&self) -> &InnerSort<'bump> {
//         self.precise_as_ref()
//     }
// }

// impl<'bump> CanBeAllocated<'bump> for Sort<'bump> {
//     type Inner = InnerSort<'bump>;

//     fn allocate<A>(allocator: &'bump A, inner: Self::Inner) -> Self
//     where
//         A: ScopeAllocator<'bump, Self::Inner> + 'bump,
//     {
//         let inner = unsafe {
//             let ptr = allocator.alloc();
//             std::ptr::write(ptr.as_ptr(), inner);
//             ptr
//         };
//         Sort {
//             inner,
//             container: PhantomData::default(),
//         }
//     }
// }

// impl<'bump> From<&'bump InnerSort<'bump>> for Sort<'bump> {
//     fn from(value: &'bump InnerSort<'bump>) -> Self {
//         Sort {
//             inner: NonNull::from(value),
//             container: Default::default(),
//         }
//     }
// }

// impl<'bump> FromNN<'bump> for Sort<'bump> {
//     type Inner = InnerSort<'bump>;

//     unsafe fn from_nn(inner: NonNull<Self::Inner>) -> Self {
//         Self {
//             inner,
//             container: Default::default(),
//         }
//     }
// }

pub fn new_static_sort(
    // name: &str,
    // flags: SFlags,
    // evaluated: Option<Sort<'static>>,
    inner: InnerSort<'static>,
) -> Sort<'static> {
    // .unwrap();
    // Sort {
    //     inner,
    //     container: Default::default(),
    // }
    // Sort::new_from(&StaticContainer, inner)
    StaticContainer.alloc_inner(inner)
}

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerSort<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        match self {
            InnerSort::Base(b) => b.name(),
            InnerSort::UserEvaluatable(ue) => ue.name(),
            InnerSort::Index(idx) => idx.name(),
        }
    }
}
