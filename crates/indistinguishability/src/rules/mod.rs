use itertools::chain;
#[cfg(test)]
pub use prf::test as prf_test;
pub use vampire::VampireRule;

use crate::Problem;
use crate::problem::{PRule, RcRule};

macro_rules! mk_prolog {
    ($pre:tt) => {
        mk_prolog!(@ None; $pre :-)
    };
    ($name:expr; $pre:tt) => {
        mk_prolog!(@ Some($name); $pre :-)
    };
    ($pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ None; $pre :- $($post),*)
    };
    ($name:expr; $pre:tt :- $($post:tt),*) => {
        mk_prolog!(@ Some($name); $pre :- $($post),*)
    };

    (@ $name:expr; $pre:tt :- $($post:tt),*) => {
        ::golgge::PrologRule::builder()
            .input($crate::rexp!($pre).into_iter().collect())
            .deps([$($crate::rexp!($post).into_iter().collect()),*])
            .maybe_name($name)
            .build()
            .unwrap()
    };
}

pub(crate) mod base_rules;
mod prf;
pub use prf::PRF;

pub mod utils;

mod nonce;
pub use nonce::{FreshNonce, mk_no_guessing_smt};

mod deduce;
mod substitution;

mod vampire;

#[cfg(debug_assertions)]
mod sanity_check;

pub fn mk_default_prolog_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> {
    chain![
        [
            #[cfg(debug_assertions)]
            {
                sanity_check::SanityCheck.into_mrc()
            }
        ],
        pbl.extra_rules().iter().cloned(),
        deduce::mk_rules(pbl).map(|x| x.into_mrc()),
        [substitution::SubstRule.into_mrc()]
    ]
}
