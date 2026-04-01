use itertools::{Itertools, chain};
use logic_formula::AsFormula;
use quarck::CowArc;
use rustc_hash::FxHashSet;
use utils::match_eq;

use crate::rexp;
use crate::terms::{AND, EQ, FOBinder, Formula, IMPLIES, MITE, NOT, OR, Variable};

#[derive(Debug, Clone)]
struct CondFormula {
    pub vars: Vec<Variable>,
    pub cond: Formula,
    pub f: Formula,
}

fn inner_split(current: CondFormula, todo: &mut Vec<CondFormula>, ret: &mut Vec<CondFormula>) {
    match &current.f {
        Formula::Quantifier {
            head: FOBinder::Forall,
            vars: fvars,
            arg,
        } => {
            let CondFormula { vars, cond, .. } = current;
            todo.push(CondFormula {
                vars: chain![vars, fvars.iter().cloned()].collect(),
                cond,
                f: arg[0].clone(),
            });
        }
        Formula::App { head, args } if head == &AND => {
            let (a, b) = args.iter().cloned().collect_tuple().unwrap();
            todo.push(CondFormula {
                f: a,
                ..current.clone()
            });
            todo.push(CondFormula { f: b, ..current });
        }
        Formula::App { head, args } if head == &IMPLIES => {
            let (a, b) = args.iter().cloned().collect_tuple().unwrap();
            todo.push(CondFormula {
                f: b,
                cond: AND.rapp([a, current.cond.clone()]),
                ..current
            });
        }
        _ => {
            ret.push(current);
        }
    }
}

impl CondFormula {
    pub fn into_formula(self) -> Formula {
        let Self { vars, cond, f } = self;
        let inner = match cond.try_evaluate() {
            Some(true) => f,
            Some(false) => !f,
            _ => rexp!((=> #cond #f)),
        };
        if vars.is_empty() {
            inner
        } else {
            rexp!((forall #vars #inner))
        }
    }
}

impl Formula {
    pub fn into_iter_conjunction(self) -> impl Iterator<Item = Self> {
        let mut todo = vec![CondFormula {
            vars: vec![],
            cond: Self::True(),
            f: self.clone(),
        }];
        let mut ret = Vec::new();

        while let Some(current) = todo.pop() {
            inner_split(current, &mut todo, &mut ret);
        }

        ret.into_iter().map(CondFormula::into_formula)
    }
}
