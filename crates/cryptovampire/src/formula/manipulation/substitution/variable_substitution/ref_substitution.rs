use itertools::Itertools;
use utils::vecref::VecRefClone;

use super::OneVarSubst;
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::manipulation::Substitution;
use crate::formula::variable::{Variable, uvar};

/// Immutable version of [super::MultipleVarSubst] that allows for easy cloning.
///
/// It makes use of [VecRefClone] under the hood instead of [Vec]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenMultipleVarSubst<'a, T: Clone> {
    content: VecRefClone<'a, OneVarSubst<T>>,
}

impl<'a, T: Clone> FrozenMultipleVarSubst<'a, T> {
    pub fn new<VRC: Into<VecRefClone<'a, OneVarSubst<T>>>>(content: VRC) -> Self {
        Self {
            content: content.into(),
        }
    }

    pub fn content(&self) -> &VecRefClone<'a, OneVarSubst<T>> {
        &self.content
    }
}

impl<'a, A: Clone> FromIterator<OneVarSubst<A>> for FrozenMultipleVarSubst<'a, A> {
    fn from_iter<T: IntoIterator<Item = OneVarSubst<A>>>(iter: T) -> Self {
        Self {
            content: iter.into_iter().collect(),
        }
    }
}

/// Immutable substitution of multiple variable. It is functionnally the same as [FrozenMultipleVarSubst]
///
/// The content must follow the invariant checked by [Self::valid]
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenSubst<'a, T: Clone> {
    vars: VecRefClone<'a, uvar>,
    formulas: VecRefClone<'a, T>,
}

impl<'a, T: Clone> FrozenSubst<'a, T> {
    pub fn new(vars: VecRefClone<'a, uvar>, formulas: VecRefClone<'a, T>) -> Self {
        Self { vars, formulas }
    }

    pub fn new_from<VRCuvar, VCRT>(var: VRCuvar, formulas: VCRT) -> Self
    where
        VRCuvar: Into<VecRefClone<'a, uvar>>,
        VCRT: Into<VecRefClone<'a, T>>,
    {
        let r = Self {
            vars: var.into(),
            formulas: formulas.into(),
        };
        r.assert_valid();
        r
    }
    pub fn vars(&self) -> &VecRefClone<'a, uvar> {
        &self.vars
    }

    pub fn formulas(&self) -> &VecRefClone<'a, T> {
        &self.formulas
    }

    /// panics if not valid
    pub fn assert_valid(&self) {
        assert_eq!(self.vars.len(), self.formulas.len())
    }

    /// Check that the [FrozenSubst], that is [FrozenSubst::vars] and [FrozenSubst::formulas] are the same length
    ///
    /// In debug mode, it checks for the unicity of all varibles as well
    pub fn valid(&self) -> bool {
        self.vars.len() == self.formulas.len()
            && if cfg!(debug_assertions) {
                self.vars.iter().all_unique()
            } else {
                true
            }
    }
}

impl<'a, 'bump> FrozenMultipleVarSubst<'a, Variable<'bump>> {
    pub fn get_var(&self, var: &Variable<'bump>) -> Variable<'bump> {
        self.content()
            .into_iter()
            .find(|ovs| ovs.id() == var.id)
            .map(|ovs| *ovs.f())
            .unwrap_or(*var)
    }
}

impl<'a, T: Clone> Default for FrozenMultipleVarSubst<'a, T> {
    fn default() -> Self {
        Self {
            content: Default::default(),
        }
    }
}

impl<'a, T: Clone> Default for FrozenSubst<'a, T> {
    fn default() -> Self {
        Self {
            vars: Default::default(),
            formulas: Default::default(),
        }
    }
}

impl<'a, T: Clone> From<FrozenMultipleVarSubst<'a, T>> for FrozenSubst<'a, T> {
    fn from(value: FrozenMultipleVarSubst<'a, T>) -> Self {
        let (vars, formulas): (Vec<_>, Vec<_>) = value
            .content
            .into_iter()
            .map(|OneVarSubst { id, f }| (id, f))
            .unzip();
        Self::new_from(vars, formulas)
    }
}

impl<'a, T: Clone> From<FrozenSubst<'a, T>> for FrozenMultipleVarSubst<'a, T> {
    fn from(FrozenSubst { vars, formulas }: FrozenSubst<'a, T>) -> Self {
        // let FrozenSubst { vars, formulas } = value;
        // assert_eq!(vars.len(), formulas.len());
        let content: Vec<OneVarSubst<_>> =
            vars.into_iter().zip_eq(formulas).map_into().collect_vec();
        Self::new(content)
    }
}

pub type FrozenOVSubstF<'a, 'bump> = FrozenMultipleVarSubst<'a, ARichFormula<'bump>>;
impl<'a, 'bump: 'a> Substitution<'bump> for FrozenOVSubstF<'a, 'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        self.content()
            .into_iter()
            .find(|ovs| ovs.id() == var.id)
            .map(|ovs| ovs.get(var))
            .unwrap_or(RichFormula::Var(*var).into())
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for FrozenMultipleVarSubst<'a, Variable<'bump>> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        // self.content()
        //     .into_iter()
        //     .find(|ovs| ovs.id() == var.id)
        //     .map(|ovs| ovs.f().into())
        //     .unwrap_or(RichFormula::Var(*var).into())
        self.get_var(var).into()
    }
}

pub type FrozenSubstF<'a, 'bump> = FrozenSubst<'a, ARichFormula<'bump>>;
impl<'a, 'bump: 'a> Substitution<'bump> for FrozenSubstF<'a, 'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        let FrozenSubst { vars, formulas, .. } = self;
        vars.iter()
            .zip_eq(formulas.iter())
            .find(|(&id, _)| id == var.id)
            .map(|(_, f)| f.clone())
            .unwrap_or(RichFormula::Var(*var).into())
    }
}
