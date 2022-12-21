use std::collections::{HashMap, HashSet};
use std::fmt;

use super::{function::Function, quantifier::Quantifier, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula {
    Var(Variable),
    Fun(Function, Vec<RichFormula>),
    Quantifier(Quantifier, Vec<RichFormula>),
}

#[derive(Debug, PartialOrd, Ord, Hash, Clone)]
pub struct Variable {
    pub id: usize,
    pub sort: Sort,
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X{}", self.id)
    }
}

impl PartialEq for Variable {
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

impl Eq for Variable {}

use super::builtins::functions::{f_and, f_false, f_or, f_true, AND, FALSE, NOT, OR, TRUE};
impl RichFormula {
    pub fn get_sort(&self) -> &Sort {
        match self {
            RichFormula::Var(v) => &v.sort,
            RichFormula::Fun(f, _) => f.get_output_sort(),
            RichFormula::Quantifier(q, _) => q.get_output_sort(),
        }
    }

    pub fn get_free_vars(&self) -> Vec<&Variable> {
        let mut r = Vec::new();
        let mut bounded = Vec::new();

        fn aux<'a>(bounded: &mut Vec<&'a Variable>, r: &mut Vec<&'a Variable>, t: &'a RichFormula) {
            match t {
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(bounded, r, f)),
                RichFormula::Var(v) if !bounded.contains(&v) => {
                    dbg!(&v);
                    r.push(v)},
                RichFormula::Quantifier(q, args) => {
                    let vars = q.get_variables();
                    let n = vars.len();
                    assert!(!vars.iter().any(|v| bounded.contains(&v)));
                    bounded.extend(vars.into_iter());
                    args.iter().for_each(|f| aux(bounded, r, f));
                    bounded.truncate(bounded.len() - n);
                }
                _ => {}
            }
        }
        aux(&mut bounded, &mut r, self);
        r
    }

    pub fn get_used_variables(&'_ self) -> HashSet<&'_ Variable> {
        fn aux<'a>(data: &mut HashSet<&'a Variable>, f: &'a RichFormula) {
            match f {
                RichFormula::Var(v) => {
                    data.insert(v);
                }
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(data, f)),
                RichFormula::Quantifier(q, args) => {
                    data.extend(q.get_variables().iter().map(|v| v));
                    args.iter().for_each(|f| aux(data, f))
                }
            }
        }

        let mut data = HashSet::new();
        aux(&mut data, self);
        data
    }

    pub fn apply(self, var: &Variable, f: &Self) -> Self {
        match self {
            RichFormula::Var(v) if &v == var => f.clone(),
            RichFormula::Fun(fun, args) => RichFormula::Fun(
                fun,
                args.into_iter().map(|old_f| old_f.apply(var, f)).collect(),
            ),
            RichFormula::Quantifier(q, args) => RichFormula::Quantifier(
                q,
                args.into_iter().map(|old_f| old_f.apply(var, f)).collect(),
            ),
            _ => self,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &RichFormula> {
        let mut pile = vec![self];
        std::iter::from_fn(move || {
            if let Some(f) = pile.pop() {
                match f {
                    RichFormula::Var(_) => {}
                    RichFormula::Fun(_, args) => pile.extend(args.iter()),
                    RichFormula::Quantifier(_, args) => pile.extend(args.iter()),
                }
                Some(f)
            } else {
                None
            }
        })
    }
}

impl Variable {
    pub fn new(id: usize, sort: Sort) -> Self {
        Self { id, sort }
    }
}

pub fn sorts_to_variables<'a>(from: usize, s: impl Iterator<Item = &'a Sort>) -> Vec<Variable> {
    s.enumerate()
        .map(|(i, s)| Variable::new(i + from, s.clone()))
        .collect()
}
