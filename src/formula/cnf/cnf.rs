use core::fmt;
use std::{collections::HashMap, error::Error};

use crate::formula::{env::Environement, sort::Sort};

use super::{
    super::{
        formula::{RichFormula as F, Variable},
        function::Function,
    },
    clause::Clause,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuantizedCNF {
    pub variables: Vec<Variable>,
    pub skolems: Vec<Function>,
    pub clauses: Vec<Clause>,
}

impl QuantizedCNF {
    pub fn from_formula(env: Environement, f: F) -> Self {
        todo!()
    }

    fn and(ctx: &mut Environement, mut a: Self, b: Self) -> Self {
        let QuantizedCNF {
            variables,
            skolems,
            clauses,
        } = b;
        a.extend_variables(variables.into_iter());
        a.extend_skolem(skolems.into_iter());
        a.extend_clauses(clauses.into_iter());
        a
    }

    fn or(ctx: &mut Environement, mut a: Self, b: Self) -> Self {
        let QuantizedCNF {
            variables,
            skolems,
            clauses,
        } = b;
        a.extend_variables(variables.into_iter());
        a.extend_skolem(skolems.into_iter());

        let mut new_clauses = Vec::with_capacity(a.clauses.len() * clauses.len());
        for cb in clauses.iter() {
            for ca in a.clauses.iter() {
                new_clauses.push(cb + ca)
            }
        }
        QuantizedCNF {
            clauses: new_clauses,
            ..a
        }
    }

    fn not(ctx: &mut Environement, a: Self) -> Self {
        let QuantizedCNF {
            variables,
            skolems,
            clauses,
        } = a;

        let n = clauses.len();

        let iter = std::iter::successors(Some(vec![0; n]), |indices| {
            let mut indices = indices.clone();

            let mut i = 0;
            while i < n && indices[i] >= (clauses[i].litterals().len() - 1) {
                indices[i] = 0;
                i += 1;
            }
            if i == n {
                None
            } else {
                indices[i] += 1;
                Some(indices)
            }
        })
        .map(|indices| {
            indices
                .iter()
                .enumerate()
                .map(|(i, &j)| clauses[i].litterals()[j].clone())
                .collect()
        });
        QuantizedCNF {
            variables,
            skolems,
            clauses: iter.collect(),
        }
    }

    fn extend_variables(&mut self, iter: impl Iterator<Item = Variable>) {
        for v in iter {
            if !self.variables.contains(&v) {
                self.variables.push(v)
            }
        }
    }

    fn extend_skolem(&mut self, iter: impl Iterator<Item = Function>) {
        for f in iter {
            debug_assert!(f.is_skolem());
            if !self.skolems.contains(&f) {
                self.skolems.push(f)
            }
        }
    }

    fn extend_clauses(&mut self, iter: impl Iterator<Item = Clause>) {
        self.clauses.extend(iter)
    }
}
