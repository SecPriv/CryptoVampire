pub mod builtin;
pub mod dispacher;
pub mod inner;
pub mod name_caster_collection;
pub mod signature;
pub mod traits;

#[allow(clippy::module_inception)]
mod function;

use core::fmt::Debug;
// pub mod equality;
use std::hash::Hash;

pub use function::{Function, new_static_function};
// use crate::problem::step::Step;
use utils::{variants, variants_ref_try_into};

use self::{
    inner::{
        booleans::Booleans,
        evaluate::Evaluate,
        evaluated_fun::EvaluatedFun,
        if_then_else::IfThenElse,
        name::Name,
        // nonce::Nonce,
        predicate::Predicate,
        skolem::Skolem,
        step::StepFunction,
        subterm::Subterm,
        term_algebra::TermAlgebra,
        unused::Tmp,
    },
    traits::{MaybeEvaluatable, MaybeFixedSignature},
};

// const BASE_SKOLEM_NAME: &'static str = "m$sk_";
// bitflags! {
//     #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
//     pub struct FFlags: u32 {
//         /// is a step
//         const FROM_STEP =           1<<0 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();
//         /// is a skolem
//         const SKOLEM =              1<<1;
//         /// is a find such that
//         // const FIND_SUCH_THAT =      1<<2;
//         const FROM_QUANTIFIER =     1<<2;
//         /// introduced by the user
//         const USER_DEFINED =        1<<3;
//         /// will be defined as part as the term algebra in smt
//         /// and will have its sorts turned into the ta sorts
//         const TERM_ALGEBRA =        1<<4;
//         /// is the evaluate equivalent of a [`Flags::TERM_ALGEBRA`]
//         const EVALUATE_TA =         1<<5;
//         /// automations will skip this function when generating the
//         /// translation for ta to evaluate
//         const SPECIAL_EVALUATE =    1<<6;

//         const DESTRUCTOR =          1<<7 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();

//         const BUILTIN =             1<<8;

//         const SUBTERM_FUN =         1<<9;

//         const SPLITING =            1<<10;

//         const SPECIAL_SUBTERM =     1<<11;

//         const CELL =                1<<12 | FFlags::SPECIAL_EVALUATE.bits() | FFlags::SPECIAL_SUBTERM.bits() | FFlags::TERM_ALGEBRA.bits();

//     }
// }

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum InnerFunction<'bump> {
    /// Boolean connective like `and`, `or`, `=`, etc...
    /// Basically the builtin functions that have type
    /// [BOOL](crate::formula::sort::builtins::BOOL).
    Bool(Booleans),
    /// The [Step](crate::problem::step)s
    Step(StepFunction<'bump>),
    /// A subterm function. By it a `vampire` special one, or a pure FOL one
    Subterm(Subterm<'bump>),
    /// Term algebra functions and their evaluated form
    ///
    /// This means all the user-defined function and all the other BC functions
    TermAlgebra(TermAlgebra<'bump>),
    /// The `ite` from smt
    IfThenElse(IfThenElse),
    /// To cast from term algebra to the evaluated space
    Evaluate(Evaluate<'bump>),
    /// Other predicates
    Predicate(Predicate<'bump>),
    /// When you need to define a function but not use it
    Tmp(Tmp<'bump>),
    Skolem(Skolem<'bump>),

    Name(Name<'bump>),

    EvaluatedFun(EvaluatedFun<'bump>),
}

impl<'bump> InnerFunction<'bump> {
    variants!(InnerFunction;
        Bool:Booleans,
        // Nonce:Nonce<'bump>,
        Step:StepFunction<'bump>,
        Subterm:Subterm<'bump>,
        TermAlgebra:TermAlgebra<'bump>,
        IfThenElse:IfThenElse,
        Evaluate:Evaluate<'bump>,
        Predicate:Predicate<'bump>,
        Tmp:Tmp<'bump>,
        Skolem:Skolem<'bump>,
        // Invalid:InvalidFunction,
    );
}

variants_ref_try_into!(InnerFunction : InnerFunction<'bump> => {
    Bool:Booleans|
    // Nonce:Nonce<'bump>|
    Step:StepFunction<'bump>|
    Subterm:Subterm<'bump>|
    TermAlgebra:TermAlgebra<'bump>|
    IfThenElse:IfThenElse|
    Evaluate:Evaluate<'bump>|
    Predicate:Predicate<'bump>|
    Tmp:Tmp<'bump>|
    Skolem:Skolem<'bump>
    // Invalid:InvalidFunction
};
    'bump
);

impl<'bump> MaybeEvaluatable<'bump> for InnerFunction<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        match self {
            Self::Bool(x) => x.maybe_get_evaluated(),
            Self::Step(x) => x.maybe_get_evaluated(),
            Self::Subterm(x) => x.maybe_get_evaluated(),
            Self::TermAlgebra(x) => x.maybe_get_evaluated(),
            Self::IfThenElse(x) => x.maybe_get_evaluated(),
            Self::Evaluate(x) => x.maybe_get_evaluated(),
            Self::Predicate(x) => x.maybe_get_evaluated(),
            Self::Tmp(x) => x.maybe_get_evaluated(),
            Self::Skolem(x) => x.maybe_get_evaluated(),
            Self::EvaluatedFun(x) => x.maybe_get_evaluated(),
            Self::Name(x) => x.maybe_get_evaluated(),
        }
    }
}

impl<'a, 'bump> MaybeFixedSignature<'a, 'bump> for InnerFunction<'bump>
where
    'bump: 'a,
    Self: 'a,
{
    fn maybe_fixed_signature(&'a self) -> Option<signature::FixedRefSignature<'a, 'bump>> {
        match self {
            Self::Bool(x) => x.maybe_fixed_signature(),
            Self::Step(x) => x.maybe_fixed_signature(),
            Self::Subterm(x) => x.maybe_fixed_signature(),
            Self::TermAlgebra(x) => x.maybe_fixed_signature(),
            Self::IfThenElse(x) => x.maybe_fixed_signature(),
            Self::Evaluate(x) => x.maybe_fixed_signature(),
            Self::Predicate(x) => x.maybe_fixed_signature(),
            Self::Tmp(x) => x.maybe_fixed_signature(),
            Self::Skolem(x) => x.maybe_fixed_signature(),
            Self::EvaluatedFun(x) => x.maybe_fixed_signature(),
            Self::Name(x) => x.maybe_fixed_signature(),
        }
    }
}

// match_as_trait!(self => {
//     Self::Bool(x)
//     | Self::Step(x)
//     | Self::Subterm(x)
//     | Self::TermAlgebra(x)
//     | Self::IfThenElse(x)
//     | Self::Evaluate(x)
//     | Self::Predicate(x)
//     | Self::Tmp(x)
//     | Self::Skolem(x)
//  => {x.maybe_fixed_signature()}})
