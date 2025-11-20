use ::egg::Id;
use logic_formula::{AsFormula, Destructed};
use serde::Serialize;
use smallvec::SmallVec;
use steel_derive::Steel;

use crate::terms::{Function, Variable};

mod egg;
// mod egg_like;
mod base;
// mod rec_exp_lang;
mod sexpr;

mod builders;
mod manipulation;
mod steel;
pub use manipulation::{AlphaArgs, Substitution};
/// Re-exports `InnerLang`, the language used for `egg` e-graphs.
pub(crate) use smt::QuantifierTranslator;
/// Re-exports `RecFOFormula`, a recursive first-order formula representation.
/// Re-exports `substitution_utils`, a module containing utilities for substitution.
pub(crate) mod list;

mod binder;
pub use binder::{RecFOFormulaQuant, RecFOFormulaQuantRef};

mod printing;
mod smt;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Steel, Serialize)]
#[steel(equality, hash)]
pub enum Formula {
    Quantifier {
        head: FOBinder,
        vars: cowarc![Variable],
        arg: cowarc![Self],
    },
    App {
        head: Function,
        args: cowarc![Self],
    },
    Var(Variable),
}

mod conversion;

const SIZE: usize = 3;
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Serialize)]
pub struct InnerLang {
    pub head: Function,
    pub args: SmallVec<[Id; SIZE]>,
}

/// Represents the type of a first-order logic binder (quantifier).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Steel, Serialize)]
pub enum FOBinder {
    /// Universal quantifier (for all).
    Forall,
    /// Existential quantifier (there exists).
    Exists,
    /// Find such that quantifier.
    FindSuchThat,
}

/// A trait for types that can be treated as a formula.
pub trait FormulaLike {
    /// The concrete formula type.
    type F<'a>: AsFormula
    where
        Self: 'a;
    /// Converts `self` into a concrete formula type.
    fn as_formula(&self) -> Self::F<'_>;

    /// Destructs the formula into its head and arguments.
    fn destruct(&self) -> Destructed<Self::F<'_>, impl Iterator<Item = Self::F<'_>>> {
        self.as_formula().destruct()
    }
}
