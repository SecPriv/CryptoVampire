mod parse;

use egg::{ENodeOrVar, Var};
pub use rewrites::mk_rewrites_rules;
mod rewrites;

pub use deduce::mk_deduce_rules;
use utils::implvec;
mod deduce;


#[cfg(test)]
mod test;


fn var_as_recexpr<'a, L>(vars: implvec!(&'a Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}