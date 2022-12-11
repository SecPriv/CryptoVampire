
use core::fmt;
use std::{collections::HashMap, error::Error};

use crate::formula::sort::Sort;

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
    naming_min_size: usize,
    naming_current: usize
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
        let (mut a, b) = ord_utils::sort(a, b); // a < b
        let QuantizedCNF {
            variables,
            skolems,
            clauses
        } = a;
        if b.clauses.len() > ctx.naming_min_size() {
            
        }
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
    fn naming_min_size(&self) -> usize {
        self.naming_min_size
    }

    fn is_name_free(&self, name: &str) -> bool {
        self.functions.contains_key(&name.to_owned())
    }

    /// if it returns something, you messed up
    fn add_function(&mut self, f: Function) -> Option<Function> {
        self.functions.insert(f.name().to_owned(), f)
    }

    fn add_naming_function(&mut self, free_sorts: impl Iterator<Item = Sort>, out_sort: Sort) -> Function {
        let name = format!("_SP{}", self.naming_current);
        let fun = Function::new(&name, free_sorts.collect(), out_sort);
        self.add_function(fun).unwrap();
        fun
    }
}