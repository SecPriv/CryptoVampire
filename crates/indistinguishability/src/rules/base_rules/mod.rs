mod parse;

use egg::{ENodeOrVar, Var};
use itertools::chain;
pub use rewrites::mk_rewrites_rules;
mod rewrites;

use utils::implvec;

use crate::Problem;
use crate::problem::{PRule, RcRule};
use crate::terms::NOT;


#[cfg(test)]
mod test;

fn var_as_recexpr<'a, L>(vars: implvec!(&'a Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}
