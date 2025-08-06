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
use egg::Analysis;
use golgge::{Dependancy, Rule};
use itertools::chain;
pub use prf::PRF;

pub mod utils;

mod nonce;
pub use nonce::{FreshNonce, mk_no_guessing_smt};

mod deduce;
mod substitution;

mod vampire;
#[cfg(test)]
pub use prf::test as prf_test;
pub use vampire::VampireRule;

use crate::problem::{PRule, RcRule};
use crate::{Lang, Problem};

pub fn mk_default_prolog_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> {
    chain![
        [
            #[cfg(debug_assertions)]
            {
                SanityCheck.into_mrc()
            }
        ],
        pbl.extra_rules().iter().cloned(),
        deduce::mk_rules(pbl).map(|x| x.into_mrc()),
        [substitution::SubstRule.into_mrc()]
    ]
}

struct SanityCheck;

impl<N: Analysis<Lang>> Rule<Lang, N> for SanityCheck {
    fn search(&self, pblm: &mut golgge::Program<Lang, N>, _: egg::Id) -> golgge::Dependancy {
        let egraph = pblm.egraph_mut();
        use logic_formula::egg::SimpleDiscriminant;

        use crate::terms::{FALSE, TRUE};

        let mtrue = TRUE.app_empty();
        let mfalse = FALSE.app_empty();
        let x = egraph.equivs(&mtrue, &mfalse);
        if !x.is_empty() {
            eprintln!("true = false");
            eprintln!(
                "{}",
                egraph
                    .explain_equivalence(&mtrue, &mfalse)
                    .get_flat_string()
            );
            panic!("wtf")
        }

        Dependancy::impossible()
    }
}
