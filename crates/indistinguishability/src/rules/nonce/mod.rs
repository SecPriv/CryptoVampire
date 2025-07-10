//! Nonce freshness

use crate::{Lang, terms::RecFOFormula};
use egg::{Analysis, EGraph, Id};

declare_trace!($"nonce_fresh");

pub use deduce_fresh::FreshNonce;
mod deduce_fresh;

pub use searcher::Nonce;
mod searcher;

fn convert_id<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> RecFOFormula {
    RecFOFormula::try_from_id(egraph, id).unwrap()
}

pub use smt_no_guessing::mk_no_guessing_smt;
mod smt_no_guessing;

#[cfg(test)]
mod test;
