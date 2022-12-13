use std::{collections::VecDeque, error::Error, fmt};

use crate::formula::{
    formula::{Formula as F, Variable},
    function::Function,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Litteral {
    Var(Variable),
    Fun(Function, Vec<Litteral>),
}

impl Litteral {
    pub fn get_var(&self) -> Option<&Variable> {
        match self {
            Litteral::Var(v) => Some(v),
            _ => None,
        }
    }

    pub fn is_var(&self) -> bool {
        self.get_var().is_some()
    }

    pub fn get_fun(&self) -> Option<(&Function, &Vec<Litteral>)> {
        match self {
            Litteral::Fun(f, args) => Some((f, args)),
            _ => None,
        }
    }

    pub fn is_fun(&self) -> bool {
        self.get_fun().is_some()
    }

    pub fn variables_iter(&self) -> impl Iterator<Item = &Variable> {
        self.into_iter().filter_map(Self::get_var)
    }

    pub fn functions_iter(&self) -> impl Iterator<Item = &Function> {
        self.into_iter().filter_map(Self::get_fun).map(|(f, _)| f)
    }
}

impl TryFrom<F> for Litteral {
    type Error = ConversionError;

    fn try_from(value: F) -> Result<Self, Self::Error> {
        match value {
            F::Var(v) => Ok(Litteral::Var(v)),
            F::Fun(f, args) => {
                let args: Result<Vec<Litteral>, Self::Error> =
                    args.into_iter().map(|f| f.try_into()).collect();
                let args = args?;
                Ok(Litteral::Fun(f, args))
            }
            F::Quantifier(_, _) => Err(ConversionError),
        }
    }
}

#[derive(Debug)]
pub struct ConversionError;

impl Error for ConversionError {}

impl fmt::Display for ConversionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "no quantifier allowed")
    }
}

pub struct SubtermIterator<'a>(Vec<&'a Litteral>);

impl<'a> Iterator for SubtermIterator<'a> {
    type Item = &'a Litteral;

    fn next(&mut self) -> Option<Self::Item> {
        match self.0.pop() {
            None => None,
            Some(l @ Litteral::Var(_)) => Some(l),
            Some(l @ Litteral::Fun(_, args)) => {
                self.0.extend(args.iter());
                Some(l)
            }
        }
    }
}

impl<'a> IntoIterator for &'a Litteral {
    type Item = Self;

    type IntoIter = SubtermIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        SubtermIterator(vec![&self])
    }
}
