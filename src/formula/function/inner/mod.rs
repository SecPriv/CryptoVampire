use crate::utils::{string_ref::StrRef, traits::RefNamed};

use super::InnerFunction;

// pub mod base_function;
pub mod booleans;
pub mod evaluate;
// pub mod function_like;
pub mod if_then_else;
pub mod invalid_function;
// pub mod nonce;
pub mod predicate;
pub mod skolem;
pub mod step;
pub mod subterm;
pub mod term_algebra;
pub mod unused;

impl<'a, 'bump: 'a> RefNamed<'a> for &'a InnerFunction<'bump> {
    fn name_ref(&self) -> StrRef<'a> {
        todo!()
    }
}
