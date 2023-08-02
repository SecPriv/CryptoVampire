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

/// Something that knows the [Realm] we are in
///
/// This is useful for configuration structs
pub trait KnowsReaml {
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

impl KnowsReaml for () {
    fn get_realm(&self) -> Realm {
        Default::default()
    }
}

impl KnowsReaml for Realm {
    fn get_realm(&self) -> Realm {
        *self
    }
}
