mod parse;

use std::rc::Rc;

use egg::{ENodeOrVar, Var};
use golgge::{PrologRule, Rule};
use itertools::chain;
pub use rewrites::mk_rewrites_rules;
mod rewrites;

pub use equiv::mk_equiv_rules;
use utils::implvec;

use crate::{
    Lang, Problem,
    problem::{PRule, RcRule},
};
mod equiv;

pub fn mk_prolog_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> {
    chain![
        pbl.extra_rules().iter().cloned(),
        mk_equiv_rules(pbl).map(|x| x.into_mrc())
    ]
}

#[cfg(test)]
mod test;

fn var_as_recexpr<'a, L>(vars: implvec!(&'a Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}
