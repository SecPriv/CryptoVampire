use std::fmt;
use std::ops::{Add, Deref};

use itertools::Itertools;
use utils::utils::MaybeInvalid;

use super::formula::{ARichFormula, RichFormula};
use super::sort::Sort;

/// Alias for the name of varibles
#[allow(non_camel_case_types)]
pub type uvar = u16;

#[allow(clippy::derived_hash_with_manual_eq)] // <- for debug reasons
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
                assert_eq!(
                    self.sort, other.sort,
                    "{self:} ({:}) != {other:} ({:})",
                    self.sort, other.sort
                );
                true
            } else {
                false
            }
        } else {
            self.id == other.id
        }
    }
}

impl Eq for Variable<'_> {}

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

    /// see [Sort::get_id_number]
    ///
    /// Because I'm stupid
    #[inline]
    pub(crate) fn get_unique_id(&self) -> cryptovampire_smt::uvar {
        (self.id as u32) << 16 | (self.sort.get_id_number() as u32)
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
// Vec<Variable<'bump>>
where
    I: Deref<Target = Sort<'bump>>,
    I2: FromIterator<Variable<'bump>>,
{
    s.into_iter()
        .zip(0..)
        .map(|(s, i)| Variable::new(i + from, *s))
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
    fn from(arg: (uvar, &'a Sort<'bump>)) -> Self {
        let (id, sort) = arg;
        Variable { id, sort: *sort }
    }
}
impl<'bump, 'a: 'bump> From<(&'a Sort<'bump>, uvar)> for Variable<'bump> {
    fn from(arg: (&'a Sort<'bump>, uvar)) -> Self {
        let (sort, id) = arg;
        Variable { id, sort: *sort }
    }
}

fn _enlarge<'a, 'b>(q: Variable<'a>) -> Variable<'b>
where
    'a: 'b,
{
    q
}

/// To get the maxvar
pub trait IntoVariableIter<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>>;

    fn vars_id_iter(self) -> impl Iterator<Item = uvar>
    where
        Self: Sized,
    {
        self.vars_iter().map(|v| v.id)
    }

    /// find the biggest [Variable::id] or default to 0
    fn max_var(self) -> uvar
    where
        Self: Sized,
    {
        self.max_var_or_max(0)
    }

    /// find the biggest [Variable::id] that if larger than `max` or return `max`
    fn max_var_or_max(self, max: uvar) -> uvar
    where
        Self: Sized,
    {
        std::cmp::max(max, self.vars_id_iter().max().unwrap_or(max)) + 1
    }

    fn contains_var(self, Variable { id, .. }: &Variable<'bump>) -> bool
    where
        Self: Sized,
    {
        self.vars_id_iter().contains(id)
    }
}

impl<'bump, U, V> IntoVariableIter<'bump> for U
where
    U: IntoIterator<Item = V>,
    V: IntoVariableIter<'bump>,
{
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        self.into_iter().flat_map(|i| i.vars_iter())
    }
}

impl<'bump> IntoVariableIter<'bump> for Variable<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        [self].into_iter()
    }
}

impl<'a, 'bump> IntoVariableIter<'bump> for &'a Variable<'bump> {
    fn vars_iter(self) -> impl Iterator<Item = Variable<'bump>> {
        [*self].into_iter()
    }
}

impl<'bump> MaybeInvalid for Variable<'bump> {
    fn is_valid(&self) -> bool {
        self.sort().is_valid()
    }
}

/// convert [usize] to [uvar] crashing if impossible.
///
/// This is usefull when making ids for variable out of array lengths and the likes
pub fn from_usize(i: usize) -> uvar {
    uvar::try_from(i).expect("value out of range, can't make a variable out of it")
}
