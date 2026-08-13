use std::fmt::Display;

use super::FOBinder;
use crate::terms::{EXISTS, FIND_SUCH_THAT, Function, Variable};

/// Represents a quantified first-order formula with its binder and bound variables.
pub struct RecFOFormulaQuant {
    /// The type of quantifier (e.g., Forall, Exists).
    pub quantifier: FOBinder,
    /// The variables bound by this quantifier.
    pub vars: Vec<Variable>,
}

/// A reference to a quantified first-order formula with its binder and bound variables.
pub struct RecFOFormulaQuantRef<'a> {
    /// The type of quantifier (e.g., Forall, Exists).
    pub quantifier: FOBinder,
    /// A slice of variables bound by this quantifier.
    pub vars: &'a [Variable],
}

impl<'a> RecFOFormulaQuantRef<'a> {
    /// Creates a new `RecFOFormulaQuantRef`.
    pub fn new(quantifier: FOBinder, vars: &'a [Variable]) -> Self {
        Self { quantifier, vars }
    }
}

impl RecFOFormulaQuant {
    /// Creates a new `RecFOFormulaQuant`.
    pub fn new(quantifier: FOBinder, vars: Vec<Variable>) -> Self {
        Self { quantifier, vars }
    }
}

impl FOBinder {
    /// Attempts to convert a `Function` into an `FOBinder`.
    ///
    /// Returns `Some(FOBinder)` if the function represents a known binder (e.g., `EXISTS`, `FIND_SUCH_THAT`),
    /// otherwise returns `None`.
    pub fn try_from_function(fun: &Function) -> Option<Self> {
        fun.as_fobinder()
    }

    /// Returns the arity (number of arguments) of the binder.
    pub fn arity(&self) -> usize {
        match self {
            Self::FindSuchThat => 3,
            Self::Exists | Self::Forall => 1,
        }
    }
}

impl logic_formula::Bounder<Variable> for RecFOFormulaQuant {
    fn bounds(&self) -> impl Iterator<Item = Variable> {
        self.vars.iter().cloned()
    }
}

impl<'a> logic_formula::Bounder<&'a Variable> for RecFOFormulaQuantRef<'a> {
    fn bounds(&self) -> impl Iterator<Item = &'a Variable> {
        self.vars.iter()
    }
}

impl FOBinder {
    /// The value taken by the quantifier on an empty set
    ///
    /// ```text
    /// \exists => false
    /// \forall => true
    /// ```
    pub fn on_empty(&self) -> bool {
        match self {
            FOBinder::Forall => true,
            FOBinder::Exists => false,
            _ => todo!(),
        }
    }

    /// Returns the corresponding `Function` for the binder, if applicable.
    ///
    /// For `Forall`, this returns `None` as it doesn't have a direct function representation.
    pub fn as_function(&self) -> Option<&'static Function> {
        match self {
            FOBinder::Exists => Some(&EXISTS),
            FOBinder::FindSuchThat => Some(&FIND_SUCH_THAT),
            FOBinder::Forall => None,
        }
    }
}

impl Display for FOBinder {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FOBinder::Forall => write!(f, "forall"),
            FOBinder::Exists => write!(f, "exists"),
            FOBinder::FindSuchThat => write!(f, "find_such_that"),
        }
    }
}
