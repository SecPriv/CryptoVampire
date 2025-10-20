use egg::{Analysis, Rewrite};
use itertools::chain;

use crate::{Lang, Problem};

mod problem;
mod quantifier;
mod static_rewrites;

#[cfg(test)]
mod test;

pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![
        static_rewrites::mk_rewrites(),
        problem::mk_rewrites(pbl),
        quantifier::mk_rewrites(pbl)
    ]
}
