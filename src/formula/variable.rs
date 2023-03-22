use std::{
    fmt,
    ops::{Add, Deref},
};

use super::{formula::RichFormula, sort::Sort};

#[derive(Debug, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Variable<'bump> {
    pub id: usize,
    pub sort: Sort<'bump>,
}
impl<'bump> fmt::Display for Variable<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X{}", self.id)
    }
}

impl<'bump> PartialEq for Variable<'bump> {
    fn eq(&self, other: &Self) -> bool {
        if cfg!(debug_assertions) {
            if self.id == other.id {
                assert_eq!(self.sort, other.sort);
                true
            } else {
                false
            }
        } else {
            self.id == other.id
        }
    }
}

impl<'bump> Eq for Variable<'bump> {}

impl<'bump> Variable<'bump> {
    pub fn new(id: usize, sort: Sort<'bump>) -> Self {
        Self { id, sort }
    }

    pub fn into_formula(&self) -> RichFormula<'bump> {
        RichFormula::Var(*self)
    }

    // pub fn clone_to_formula<T, U>(&self, ctx: &T) -> U
    // where
    //     T: FormulaUser<U>,
    // {
    //     self.clone().as_formula(ctx)
    // }

    pub fn sort(&self) -> &Sort<'bump> {
        &self.sort
    }

    pub fn id(&self) -> usize {
        self.id
    }
}

impl<'bump> Add<usize> for Variable<'bump> {
    type Output = Variable<'bump>;

    fn add(self, rhs: usize) -> Self::Output {
        Variable {
            id: self.id + rhs,
            ..self
        }
    }
}

pub fn sorts_to_variables<'bump, I>(from: usize, s: impl Iterator<Item = I>) -> Vec<Variable<'bump>>
where
    I: Deref<Target = Sort<'bump>>,
{
    s.enumerate()
        .map(|(i, s)| Variable::new(i + from, s.clone()))
        .collect()
}

// impl<'bump> From<(usize, Sort<'bump>)> for Variable<'bump> {
//     fn from(arg: (usize, Sort<'bump>)) -> Self {
//         let (id, sort) = arg;
//         Variable { id, sort }
//     }
// }
// impl<'bump> From<(Sort<'bump>, usize)> for Variable<'bump> {
//     fn from(arg: (Sort<'bump>, usize)) -> Self {
//         let (sort, id) = arg;
//         Variable { id, sort }
//     }
// }

impl<'bump, 'a: 'bump> From<(usize, &'a Sort<'bump>)> for Variable<'bump> {
    fn from(arg: (usize, &'a Sort)) -> Self {
        let (id, sort) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}
impl<'bump, 'a: 'bump> From<(&'a Sort<'bump>, usize)> for Variable<'bump> {
    fn from(arg: (&'a Sort, usize)) -> Self {
        let (sort, id) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}
