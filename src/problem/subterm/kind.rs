use std::collections::BTreeMap;

use hashbrown::HashMap;

use crate::{
    environement::environement::Environement,
    formula::{
        function::Function,
        sort::{FOSort, Sort},
    },
    problem::Problem,
    utils::vecref::VecRef,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum AbsSubtermKindG<U, V> {
    Regular(U),
    Vampire(V),
}

pub type SubtermKind = AbsSubtermKindG<(), ()>;
pub type SubtermKindWSort<'bump> = AbsSubtermKindG<Sort<'bump>, ()>;
pub type SubtermKindWFunction<'bump> =
    AbsSubtermKindG<BTreeMap<FOSort<'bump>, Function<'bump>>, Function<'bump>>;
pub type SubtermKindConstr<'a, 'bump> = AbsSubtermKindG<VecRef<'a, Sort<'bump>>, ()>;

impl<U, V> AbsSubtermKindG<U, V> {
    /// Returns `true` if the subterm kind general is [`Regular`].
    ///
    /// [`Regular`]: SubtermKindGeneral::Regular
    #[must_use]
    pub fn is_regular(&self) -> bool {
        matches!(self, Self::Regular(..))
    }

    pub fn as_regular(&self) -> Option<&U> {
        if let Self::Regular(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the subterm kind general is [`Vampire`].
    ///
    /// [`Vampire`]: SubtermKindGeneral::Vampire
    #[must_use]
    pub fn is_vampire(&self) -> bool {
        matches!(self, Self::Vampire(..))
    }

    pub fn as_vampire(&self) -> Option<&V> {
        if let Self::Vampire(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_subterm_kind(&self) -> SubtermKind {
        match self {
            AbsSubtermKindG::Regular(_) => SubtermKind::Regular(()),
            AbsSubtermKindG::Vampire(_) => SubtermKind::Vampire(()),
        }
    }
}

impl<'a, 'bump> SubtermKindConstr<'a, 'bump> {
    pub fn as_constr(pbl: &'a Problem<'bump>, env: &Environement<'bump>) -> Self {
        if env.use_vampire_subterm() {
            AbsSubtermKindG::Vampire(())
        } else {
            AbsSubtermKindG::Regular(pbl.sorts.iter().filter(|s| s.is_evaluatable()).collect())
        }
    }
}

impl<U, V: Default> AbsSubtermKindG<U, V> {
    pub fn vampire() -> Self {
        Self::Vampire(Default::default())
    }
}

impl<U: Default, V> AbsSubtermKindG<U, V> {
    pub fn regular() -> Self {
        Self::Regular(Default::default())
    }
}
