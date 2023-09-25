use itertools::Itertools;

use crate::{
    formula::{
        formula::{ARichFormula, RichFormula},
        manipulation::Substitution,
        variable::Variable,
    },
    implvec,
    utils::vecref::VecRefClone,
};

use super::OneVarSubst;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenOVSubst<'a, T: Clone> {
    content: VecRefClone<'a, OneVarSubst<T>>,
}

impl<'a, T: Clone> FrozenOVSubst<'a, T> {
    pub fn new<VRC: Into<VecRefClone<'a, OneVarSubst<T>>>>(content: VRC) -> Self {
        Self {
            content: content.into(),
        }
    }

    pub fn content(&self) -> &VecRefClone<'a, OneVarSubst<T>> {
        &self.content
    }
}

impl<'a, A: Clone> FromIterator<OneVarSubst<A>> for FrozenOVSubst<'a, A> {
    fn from_iter<T: IntoIterator<Item = OneVarSubst<A>>>(iter: T) -> Self {
        Self {
            content: iter.into_iter().collect(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct FrozenSubst<'a, T: Clone> {
    vars: VecRefClone<'a, usize>,
    formulas: VecRefClone<'a, T>,
}

impl<'a, T: Clone> FrozenSubst<'a, T> {
    pub fn new(vars: VecRefClone<'a, usize>, formulas: VecRefClone<'a, T>) -> Self {
        Self { vars, formulas }
    }

    pub fn new_from<VRCusize, VCRT>(var: VRCusize, formulas: VCRT) -> Self
    where
        VRCusize: Into<VecRefClone<'a, usize>>,
        VCRT: Into<VecRefClone<'a, T>>,
    {
        let r = Self {
            vars: var.into(),
            formulas: formulas.into(),
        };
        r.assert_valid();
        r
    }
    pub fn vars(&self) -> &VecRefClone<'a, usize> {
        &self.vars
    }

    pub fn formulas(&self) -> &VecRefClone<'a, T> {
        &self.formulas
    }

    /// panics if not valid
    pub fn assert_valid(&self) {
        assert_eq!(self.vars.len(), self.formulas.len())
    }

    pub fn valid(&self) -> bool {
        self.vars.len() == self.formulas.len()
    }

    pub fn extend_clone(&self, vars_idx: implvec!(usize), content: implvec!(T)) -> Self {
        let mut new = self.clone();
        new.vars.extend(vars_idx);
        new.formulas.extend(content);
        assert!(new.valid());
        new
    }
}

impl<'a, 'bump> FrozenOVSubst<'a, Variable<'bump>> {
    pub fn get_var(&self, var: &Variable<'bump>) -> Variable<'bump> {
        self.content()
            .into_iter()
            .find(|ovs| ovs.id() == var.id)
            .map(|ovs| (*ovs.f()).into())
            .unwrap_or(*var)
    }
}

impl<'a, T: Clone> Default for FrozenOVSubst<'a, T> {
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

impl<'a, T: Clone> From<FrozenOVSubst<'a, T>> for FrozenSubst<'a, T> {
    fn from(value: FrozenOVSubst<'a, T>) -> Self {
        let (vars, formulas): (Vec<_>, Vec<_>) = value
            .content
            .into_iter()
            .map(|OneVarSubst { id, f }| (id, f))
            .unzip();
        Self::new_from(vars, formulas)
    }
}

impl<'a, T: Clone> From<FrozenSubst<'a, T>> for FrozenOVSubst<'a, T> {
    fn from(FrozenSubst { vars, formulas }: FrozenSubst<'a, T>) -> Self {
        // let FrozenSubst { vars, formulas } = value;
        // assert_eq!(vars.len(), formulas.len());
        let content: Vec<OneVarSubst<_>> = vars
            .into_iter()
            .zip_eq(formulas.into_iter())
            .map_into()
            .collect_vec();
        Self::new(content)
    }
}

pub type FrozenOVSubstF<'a, 'bump> = FrozenOVSubst<'a, ARichFormula<'bump>>;
impl<'a, 'bump: 'a> Substitution<'bump> for FrozenOVSubstF<'a, 'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        self.content()
            .into_iter()
            .find(|ovs| ovs.id() == var.id)
            .map(|ovs| ovs.get(var))
            .unwrap_or(RichFormula::Var(*var).into())
    }
}

impl<'a, 'bump: 'a> Substitution<'bump> for FrozenOVSubst<'a, Variable<'bump>> {
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
