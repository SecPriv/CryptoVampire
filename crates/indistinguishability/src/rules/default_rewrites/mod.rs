use egg::{Analysis, Rewrite};
use itertools::chain;

use crate::{Lang, Problem};

/// Provides rewrite rules specific to the problem definition.
mod problem;
/// Provides rewrite rules for quantifiers.
mod quantifier;
/// Provides static rewrite rules.
mod static_rewrites;

#[cfg(test)]
mod test;

/// Creates a set of default rewrite rules.
pub fn mk_rewrites<N: Analysis<Lang>>(
    pbl: &Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'_, N> {
    chain![
        static_rewrites::mk_rewrites(),
        problem::mk_rewrites(pbl),
        quantifier::mk_rewrites(pbl)
    ]
}
