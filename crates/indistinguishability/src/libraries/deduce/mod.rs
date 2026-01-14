use itertools::chain;

use crate::Problem;
use crate::problem::{PRule, RcRule};
use crate::terms::{BIT_DEDUCE, BOOL_DEDUCE, Function, Sort};

/// Provides rules for deducing properties of quantifiers.
mod quantifier;
/// Provides regular deduction rules.
mod regular;
/// Provides static deduction rules.
mod static_rules;

mod nonce;

pub fn mk_rules(pbl: &Problem) -> impl Iterator<Item = RcRule> + use<'_> {
    chain! {
      regular::mk_rules(pbl),
      quantifier::mk_rules(pbl),
      static_rules::mk_rules(),
      [nonce::DeduceNonceRule.into_mrc()]
    }
}

/// A trait for types that can provide a deduction function.
trait GetDeduce {
    /// Attempts to retrieve a deduction function for the given type.
    fn try_get_deduce(&self) -> Option<&'static Function>;

    /// Retrieves a deduction function for the given type, panicking if not supported.
    fn get_deduce(&self) -> &'static Function {
        match self.try_get_deduce() {
            Some(fun) => fun,
            _ => panic!("not a supported sort for deduce (should be Bitstring or Bool)"),
        }
    }
}

impl GetDeduce for Sort {
    /// Attempts to retrieve a deduction function for the given sort.
    fn try_get_deduce(&self) -> Option<&'static Function> {
        match self {
            Sort::Bool => Some(&BOOL_DEDUCE),
            Sort::Bitstring => Some(&BIT_DEDUCE),
            _ => None,
        }
    }
}

impl GetDeduce for Function {
    /// Attempts to retrieve a deduction function for the output sort of the given function.
    fn try_get_deduce(&self) -> Option<&'static Function> {
        self.signature.output.try_get_deduce()
    }
}
