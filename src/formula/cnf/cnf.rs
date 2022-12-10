
use core::fmt;
use std::{collections::HashMap, error::Error};

use super::{super::{
    formula::{Formula as F, Variable},
    function::Function,
}, clause::Clause};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuantizedCNF {
    pub variables: Vec<Variable>,
    pub skolems: Vec<Function>,
    pub clauses: Vec<Clause>,
}

pub struct Context<'a> {
    functions: &'a mut HashMap<String, Function>,
    naming: usize,
}

impl QuantizedCNF {
    // pub fn from_formula_and_functions(
    //     functions: &mut HashMap<String, Function>,
    //     f: &Litteral,
    // ) -> Self {
    //     todo!()
    // }

    fn and( ctx:&mut Context, mut a: Self, b: Self) -> Self {
        let QuantizedCNF {
            variables,
            skolems,
            clauses ,
        } = b;
        a.extend_variables(variables.into_iter());
        a.extend_skolem(skolems.into_iter());
        a.extend_clauses(clauses.into_iter());
        a
    }

    fn or(ctx:&mut Context, a: Self, b: Self) -> Self {
        let (b, mut a) = ord_utils::sort(a, b); // b < a
        let QuantizedCNF {
            variables,
            skolems,
            clauses
        } = b;
        todo!()
    }

    fn extend_variables(&mut self, iter: impl Iterator<Item = Variable>) {
        for v in iter{
            if !self.variables.contains(&v) {
                self.variables.push(v)
            }
        }
    }

    fn extend_skolem(&mut self, iter: impl Iterator<Item = Function>) {
        for f in iter{
            assert!(f.is_skolem());
            if !self.skolems.contains(&f) {
                self.skolems.push(f)
            }
        }
    }

    fn extend_clauses(&mut self, iter: impl Iterator<Item = Clause>) {
        self.clauses.extend(iter)
    }
}

impl<'a> Context<'a> {
    fn naming(&self) -> usize {
        self.naming
    }

    fn is_name_free(&self, name: &str) -> bool {
        self.functions.contains_key(&name.to_owned())
    }

    /// if it returns something, you messed up
    fn add_function(&mut self, f: Function) -> Option<Function> {
        self.functions.insert(f.name().to_owned(), f)
    }
}