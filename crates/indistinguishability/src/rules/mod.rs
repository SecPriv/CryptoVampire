use egg::ENodeOrVar;
use itertools::chain;
#[cfg(test)]
pub use prf::test as prf_test;
use ::utils::implvec;
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

macro_rules! mk_rewrite {
    ($name:expr; $from:tt => $to:tt) => {
        ::egg::Rewrite::new(
            $name,
            mk_rewrite!(@@ $from),
            mk_rewrite!(@@ $to),
        ).unwrap()
    };
    
    (@@ (#$var:tt = #$value:tt)) => {
        ::egg::MultiPattern::new(vec![{
            let [::egg::ENodeOrVar::Var(v)] = $crate::rexp!(#$var) else {
                panic!("left side of `=` should be a variable")
            };
            (v, $crate::rexp!(#$value).into_iter().collect())
        }])
    };

    (@@ ($(#$var:tt = $value:tt),+)) => {
        ::egg::MultiPattern::new(vec![$({
            let [::egg::ENodeOrVar::Var(v)] = $crate::rexp!(#$var) else {
                panic!("left side of `=` should be a variable")
            };
            (v, $crate::rexp!($value).into_iter().collect())
        }),*])
    };
    
    (@@ (#$($value:tt)+)) => {
        ::egg::Pattern::from_iter(
            $crate::rexp!(#$($value)+)
        )
    };

    (@@ $value:tt) => {
        ::egg::Pattern::from_iter(
            $crate::rexp!($value)
        )
    };
}

// pub(crate) mod base_rules;
pub mod utils;

mod deduce;
mod nonce;
mod prf;
mod substitution;
mod vampire;
pub mod default_rewrites;

pub use nonce::{FreshNonce, mk_no_guessing_smt};
pub use prf::PRF;

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

fn var_as_recexpr<'a, L>(vars: implvec!(&'a egg::Var)) -> Vec<[ENodeOrVar<L>; 1]> {
    vars.into_iter()
        .copied()
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect()
}