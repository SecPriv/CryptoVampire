use cryptovampire_macros::smt;
use cryptovampire_smt::{Smt, SmtFormula};
use itertools::chain;

use crate::{
    MSmt, Problem,
    terms::{Function, Sort},
};

mod base_axioms;
pub mod convert;
pub mod rule;
pub mod runner;

pub use base_axioms::mk_prelude;

#[test]
fn test_smt_macro() {
    let x = 2;
    let f = "t";
    let t: SmtFormula<&'static str, &'static str> = smt! {
        (forall ((#a!x "my_sort")) (f #a #a))
    };
    println!("{t}")
}
