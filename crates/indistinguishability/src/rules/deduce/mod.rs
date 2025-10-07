use egg::{ENodeOrVar, Var};
use golgge::PrologRule;
use itertools::chain;
use utils::implvec;

use crate::problem::{PRule, RcRule};
use crate::terms::{BIT_DEDUCE, BOOL_DEDUCE, Function, Sort};
use crate::{Lang, Problem};

mod quantifier;
mod regular;
mod static_rules;

pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> + use<'_> {
    chain! {
      regular::mk_rules(pbl),
    //   quantifier::mk_rules(pbl),
      static_rules::mk_rules(),
    }.map(|x| x.into_mrc())
}

trait GetDeduce {
    fn try_get_deduce(&self) -> Option<&'static Function>;

    fn get_deduce(&self) -> &'static Function {
        match self.try_get_deduce() {
            Some(fun) => fun,
            _ => panic!("not a supported sort for deduce (should be Bitstring or Bool)"),
        }
    }
}

impl GetDeduce for Sort {
    fn try_get_deduce(&self) -> Option<&'static Function> {
        match self {
            Sort::Bool => Some(&BOOL_DEDUCE),
            Sort::Bitstring => Some(&BIT_DEDUCE),
            _ => None,
        }
    }
}

impl GetDeduce for Function {
    fn try_get_deduce(&self) -> Option<&'static Function> {
        self.signature.output.try_get_deduce()
    }
}
