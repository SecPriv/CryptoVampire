use super::{function::Function, quantifier::Quantifier, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Formula {
    Var(Variable),
    Fun(Function, Vec<Formula>),
    Quantifier(Quantifier, Vec<Formula>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Variable {
    pub id: usize,
    pub sort: Sort,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CNF(Vec<Vec<Formula>>);

use super::builtins::functions::{f_and, f_false, f_or, f_true};
impl From<CNF> for Formula {
    fn from(cnf: CNF) -> Self {
        from_conjunction(cnf.0.into_iter().map(|c| from_disjunction(c.into_iter())))
    }
}

fn from_disjunction(mut dis: impl Iterator<Item = Formula>) -> Formula {
    match dis.next() {
        None => f_true(),
        Some(f) => dis.fold(f, f_or),
    }
}

fn from_conjunction(mut dis: impl Iterator<Item = Formula>) -> Formula {
    match dis.next() {
        None => f_false(),
        Some(f) => dis.fold(f, f_and),
    }
}

macro_rules! var {
    ($id:pat, $sort:pat) => {
        crate::formula::formula::Formula::Var(crate::formula::formula::Variable {
            id: $id,
            sort: $sort,
        })
    };
    ($id:expr; $sort:expr) => {
        crate::formula::formula::Formula::Var(crate::formula::formula::Variable {
            id: $id,
            sort: $sort,
        })
    };
}

macro_rules! fun {
    ($f:pat, $args:pat) => {
        crate::formula::formula::Formula::Fun($f, $args)
    };
    ($f:expr; $($args:expr),*) => {
        crate::formula::formula::Formula::Fun($f.clone(), vec![$($args,)*])
    };
}

macro_rules! quant {
    ($f:pat, $args:pat) => {
        crate::formula::formula::Formula::Quantifier($f, $args)
    };
    ($f:expr; $($args:expr),*) => {
        crate::formula::formula::Formula::Quantifier($f.clone(), vec![$($args,)*])
    };
}
pub(crate) use {fun, quant, var};

impl Formula {
    pub fn get_sort(&self) -> &Sort {
        match self {
            var!(_, s) => s,
            fun!(f, _) => f.get_output_sort(),
            quant!(q, _) => q.get_output_sort(),
        }
    }
}

impl Variable {
    pub fn new(id: usize, sort: Sort) -> Self {
        Self { id, sort }
    }
}

impl CNF {
    pub fn new(f: Vec<Vec<Formula>>) -> Self {
        CNF(f)
    }
}
