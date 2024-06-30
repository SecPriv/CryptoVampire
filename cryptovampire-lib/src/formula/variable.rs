use std::{
    fmt,
    ops::{Add, Deref},
};

use super::{
    formula::{ARichFormula, RichFormula},
    sort::Sort,
};

/// Alias for the name of varibles
#[allow(non_camel_case_types)]
pub type uvar = u32;

#[derive(Debug, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct Variable<'bump> {
    pub id: uvar,
    pub sort: Sort<'bump>,
}
impl<'bump> fmt::Display for Variable<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}X{}", self.sort.short_name(), self.id)
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
    pub fn new(id: uvar, sort: Sort<'bump>) -> Self {
        Self { id, sort }
    }

    pub fn into_formula(&self) -> RichFormula<'bump> {
        RichFormula::Var(*self)
    }

    pub fn into_aformula(&self) -> ARichFormula<'bump> {
        RichFormula::Var(*self).into()
    }

    pub fn sort(&self) -> &Sort<'bump> {
        &self.sort
    }

    pub fn id(&self) -> uvar {
        self.id
    }
}

impl<'bump> Add<uvar> for Variable<'bump> {
    type Output = Variable<'bump>;

    fn add(self, rhs: uvar) -> Self::Output {
        Variable {
            id: self.id + rhs,
            ..self
        }
    }
}

pub fn sorts_to_variables<'bump, I, I2>(from: uvar, s: impl IntoIterator<Item = I>) -> I2
//Vec<Variable<'bump>>
where
    I: Deref<Target = Sort<'bump>>,
    I2: FromIterator<Variable<'bump>>,
{
    s.into_iter()
        .zip(0..)
        .map(|(s, i)| Variable::new(i + from, s.clone()))
        .collect()
}

// impl<'bump> From<(uvar, Sort<'bump>)> for Variable<'bump> {
//     fn from(arg: (uvar, Sort<'bump>)) -> Self {
//         let (id, sort) = arg;
//         Variable { id, sort }
//     }
// }
// impl<'bump> From<(Sort<'bump>, uvar)> for Variable<'bump> {
//     fn from(arg: (Sort<'bump>, uvar)) -> Self {
//         let (sort, id) = arg;
//         Variable { id, sort }
//     }
// }

impl<'bump, 'a: 'bump> From<(uvar, &'a Sort<'bump>)> for Variable<'bump> {
    fn from(arg: (uvar, &'a Sort)) -> Self {
        let (id, sort) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}
impl<'bump, 'a: 'bump> From<(&'a Sort<'bump>, uvar)> for Variable<'bump> {
    fn from(arg: (&'a Sort, uvar)) -> Self {
        let (sort, id) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}

fn _enlarge<'a, 'b>(q: Variable<'a>) -> Variable<'b>
where
    'a: 'b,
{
    q
}
