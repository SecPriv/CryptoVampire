use crate::{
    formula::function::inner::if_then_else::IfThenElse,
    utils::{string_ref::StrRef, traits::RefNamed},
};

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
        match self {
            InnerFunction::Bool(x) => x.name().into(),
            InnerFunction::Step(x) => x.name().into(),
            InnerFunction::Subterm(x) => x.name.as_str().into(),
            InnerFunction::TermAlgebra(x) => x.name(),
            InnerFunction::IfThenElse(_x) => IfThenElse::name().into(),
            InnerFunction::Evaluate(x) => x.name().into(),
            InnerFunction::Predicate(x) => x.name().into(),
            InnerFunction::Tmp(x) => x.name().into(),
            InnerFunction::Skolem(x) => x.name().into(),
        }
    }
}
