use log::{error, log_enabled};

use super::MultipleVarSubst;
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::manipulation::Substitution;
use crate::formula::variable::{Variable, uvar};

/// A [Substitution] on only one variable
///
/// `OneVarSubst{id: x, f: y}` is the substitution $\{ x \mapsto y \}$
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct OneVarSubst<T> {
    pub id: uvar,
    pub f: T,
}

/// Shorthand for subtitions with [ARichFormula]
pub type OneVarSubstF<'bump> = OneVarSubst<ARichFormula<'bump>>;

impl<T> OneVarSubst<T> {
    pub fn id(&self) -> uvar {
        self.id
    }

    pub fn f(&self) -> &T {
        &self.f
    }

    /// Is this the identity substitution
    pub fn is_id(&self, id: uvar) -> bool {
        self.id == id
    }

    pub fn append<U>(self, value: U) -> MultipleVarSubst<T>
    where
        Self: From<U>,
    {
        [self, value.into()].into()
    }

    pub fn as_ref(&self) -> OneVarSubst<&'_ T> {
        let OneVarSubst { id, f } = self;
        OneVarSubst { id: *id, f }
    }
}

impl<T: Clone> OneVarSubst<T> {
    /// Apply [OneVarSubst::f] and then clones the result
    pub fn fc(&self) -> T {
        self.f().clone()
    }
}

impl<T> From<(uvar, T)> for OneVarSubst<T> {
    fn from((id, f): (uvar, T)) -> Self {
        Self { id, f }
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for OneVarSubstF<'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        if var.id == self.id {
            if log_enabled!(log::Level::Trace) {
                if let Ok(s) = self.f.get_sort() {
                    if s != var.sort {
                        panic!(
                            "wrong sort in substitution: subtituting {} for {s}",
                            var.sort
                        )
                    }
                } else {
                    error!("mhm...")
                }
            }
            self.f.clone()
        } else {
            RichFormula::from(*var).into()
        }
    }
}

impl<'bump> OneVarSubstF<'bump> {
    pub fn new(Variable { id, .. }: Variable<'bump>, f: ARichFormula<'bump>) -> Self {
        Self { id, f }
    }
}
