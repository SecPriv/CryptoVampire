use egg::{ENodeOrVar, Var};
use golgge::PrologRule;
use itertools::chain;
use utils::implvec;

use crate::terms::{BIT_DEDUCE, BOOL_DEDUCE, Function, Sort};
use crate::{Lang, Problem};

mod quantifier;
mod regular;
mod static_rules;

pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = PrologRule<Lang>> + use<'_> {
    chain! {
      regular::mk_rules(pbl),
      quantifier::mk_rules(pbl),
      static_rules::mk_rules()
    }
}

fn var_as_recexpr<'a, L>(vars: implvec!(&'a Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}

/// get the `deduce` function corresponding to the the sort `s`, [None] otherwise
const fn try_get_deduce(s: Sort) -> Option<&'static Function> {
    match s {
        Sort::Bool => Some(&BOOL_DEDUCE),
        Sort::Bitstring => Some(&BIT_DEDUCE),
        _ => None,
    }
}

/// [try_get_deduce] that crashes
fn get_deduce(s: Sort) -> &'static Function {
    match try_get_deduce(s) {
        Some(fun) => fun,
        _ => panic!("{s} is not a supported sort for deduce (should be Bitstring or Bool)"),
    }
}
