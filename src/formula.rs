use std::{fmt::Display, rc::Rc};

use static_init::dynamic;

use crate::utils::RcEq;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone)]
pub enum Formula<F, S> {
    Var(usize, S),
    Fun(F, Vec<Formula<F, S>>),
    Qnt(Quantifier<S>,  Vec<Formula<F, S>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Quantifier<S> {
    Forall(usize, S),
    Exists(usize, S),
    FindSt(Vec<(usize, S)>)
}

pub type RcFunction<S = RcType> = RcEq<Function<S>>;
pub type RcType = RcEq<String>;
pub type MFormula = Formula<RcFunction<RcType>, RcType>;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone)]
pub struct Function<S> {
    pub name: String,
    pub input_sorts: Vec<S>,
    pub output_sort: S,
}

impl<S> Function<S> {
    pub fn arity(&self) -> usize {
        self.input_sorts.len()
    }

    pub fn new(name: &str, input_sorts: Vec<S>, output_sort: S) -> Self {
        Function {
            name: name.to_owned(),
            input_sorts,
            output_sort,
        }
    }

    pub fn new_rc(name: &str, input_sorts: Vec<S>, output_sort: S) -> RcFunction<S> {
        Self::new(name, input_sorts, output_sort).into()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CNF<F, S>(Vec<Vec<Formula<F, S>>>);
pub type MCNF = CNF<RcFunction<RcType>, RcType>;

impl From<&str> for RcType {
    fn from(s: &str) -> Self {
        RcEq::new(s.to_owned())
    }
}

impl<S> From<Function<S>> for RcFunction<S> {
    fn from(f: Function<S>) -> Self {
        RcEq::new(f)
    }
}

#[dynamic]
pub static BOOL: RcType = "bool".into();

#[dynamic]
pub static MSG: RcType = "msg".into();

#[dynamic]
pub static NONCE: RcType = "nonce".into();

#[dynamic]
pub static AS_MSG: RcFunction = Function::new_rc("as_msg", vec![NONCE.clone()], MSG.clone());

impl MFormula {
    pub fn get_type(&self) -> RcType {
        match self {
            Formula::Var(_, s) => s.clone(),
            Formula::Fun(f, _) => f.0.output_sort.clone(),
            Formula::Qnt(_,  _) => BOOL.clone(),
        }
    }
}

impl Display for RcType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
