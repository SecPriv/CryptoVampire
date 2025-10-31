use std::fmt::Display;
use std::ops::BitAnd;

/// Are we in the lower or higher logic
#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub enum Realm {
    /// This is the symbolic realm.
    ///  - BC terms form a term algebra
    ///  - where FOL subterm is possible form any term
    ///  - evaluation must be made through a function
    ///  - ...
    ///
    /// This is the default
    #[default]
    Symbolic,
    /// This is the evaluated realm. All terms where already evaluated
    ///
    /// Notatbly `Messages` and `Bitstring` and `Condition` and `Bool` unify here
    Evaluated,
}

#[allow(dead_code)]
pub const LOW: Realm = Realm::Evaluated;
#[allow(dead_code)]
pub const HIGH: Realm = Realm::Symbolic;

impl Realm {
    /// Returns `true` if the realm is [`Evaluated`].
    ///
    /// [`Evaluated`]: Realm::Evaluated
    #[must_use]
    pub fn is_evaluated(&self) -> bool {
        matches!(self, Self::Evaluated)
    }

    /// Returns `true` if the realm is [`Symbolic`].
    ///
    /// [`Symbolic`]: Realm::Symbolic
    #[must_use]
    pub fn is_symbolic(&self) -> bool {
        matches!(self, Self::Symbolic)
    }
}

impl BitAnd for Realm {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        match self {
            Realm::Symbolic => Realm::Symbolic,
            Realm::Evaluated => rhs,
        }
    }
}

/// Something that knows the [Realm] we are in
///
/// This is useful for configuration structs
pub trait KnowsRealm {
    fn get_realm(&self) -> Realm;

    /// See [Realm::is_symbolic()]
    #[must_use]
    fn is_symbolic_realm(&self) -> bool {
        self.get_realm().is_symbolic()
    }

    /// See [Realm::is_evaluated()]
    #[must_use]
    fn is_evaluated_realm(&self) -> bool {
        self.get_realm().is_evaluated()
    }
}

impl KnowsRealm for () {
    #[inline]
    fn get_realm(&self) -> Realm {
        Default::default()
    }
}

impl KnowsRealm for Realm {
    #[inline]
    fn get_realm(&self) -> Realm {
        *self
    }
}

impl<'a, T> KnowsRealm for &'a T
where
    T: KnowsRealm,
{
    #[inline]
    fn get_realm(&self) -> Realm {
        T::get_realm(self)
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
pub struct RealmMerger<Inner, Outer>
where
    Inner: KnowsRealm,
    Outer: KnowsRealm,
{
    pub inner: Inner,
    pub outer: Outer,
}

impl<Inner, Outer> KnowsRealm for RealmMerger<Inner, Outer>
where
    Inner: KnowsRealm,
    Outer: KnowsRealm,
{
    #[inline]
    fn get_realm(&self) -> Realm {
        self.inner.get_realm() & self.outer.get_realm()
    }
}

impl Display for Realm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Realm::Symbolic => write!(f, "Symbolic"),
            Realm::Evaluated => write!(f, "Evaluated"),
        }
    }
}
