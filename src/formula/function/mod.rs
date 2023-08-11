pub mod builtin;
pub mod dispacher;
pub mod inner;
pub mod signature;
pub mod traits;

mod function;

pub use function::{new_static_function, Function};

// pub mod equality;
use std::hash::Hash;

use bitflags::bitflags;

// use crate::problem::step::Step;

use crate::{variants, variants_ref_try_into, CustomDerive};

use self::inner::{
    booleans::Booleans,
    evaluate::Evaluate,
    if_then_else::IfThenElse,
    // nonce::Nonce,
    predicate::Predicate,
    skolem::Skolem,
    step::StepFunction,
    subterm::Subterm,
    term_algebra::TermAlgebra,
    unused::Tmp,
};

use core::fmt::Debug;

// const BASE_SKOLEM_NAME: &'static str = "m$sk_";
bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug )]
    pub struct FFlags: u32 {
        /// is a step
        const FROM_STEP =           1<<0 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();
        /// is a skolem
        const SKOLEM =              1<<1;
        /// is a find such that
        // const FIND_SUCH_THAT =      1<<2;
        const FROM_QUANTIFIER =     1<<2;
        /// introduced by the user
        const USER_DEFINED =        1<<3;
        /// will be defined as part as the term algebra in smt
        /// and will have its sorts turned into the ta sorts
        const TERM_ALGEBRA =        1<<4;
        /// is the evaluate equivalent of a [`Flags::TERM_ALGEBRA`]
        const EVALUATE_TA =         1<<5;
        /// automations will skip this function when generating the
        /// translation for ta to evaluate
        const SPECIAL_EVALUATE =    1<<6;

        const DESTRUCTOR =          1<<7 | FFlags::TERM_ALGEBRA.bits() | FFlags::SPECIAL_EVALUATE.bits();

        const BUILTIN =             1<<8;

        const SUBTERM_FUN =         1<<9;

        const SPLITING =            1<<10;

        const SPECIAL_SUBTERM =     1<<11;

        const CELL =                1<<12 | FFlags::SPECIAL_EVALUATE.bits() | FFlags::SPECIAL_SUBTERM.bits() | FFlags::TERM_ALGEBRA.bits();

    }
}

use macro_attr::*;
macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone,
        CustomDerive!(maybe_evaluate, 'bump),
        CustomDerive!(maybe_fixed_signature, 'bump),
    )]
    pub enum InnerFunction<'bump> {
        #[doc="Boolean connective like `and`, `or`, `=`, etc... \
            Basically the builtin functions that have type \
            [BOOL](automator::formula::sort::builtins::BOOL)."]
        Bool(Booleans),
        // Nonce(Nonce<'bump>),
        #[doc="The [Step](automator::problem::step)s"]
        Step(StepFunction<'bump>),
        #[doc="A subterm function. By it a `vampire` special one, \
            or a pure FOL one"]
        Subterm(Subterm<'bump>),
        #[doc="Term algebra functions and their evaluated form

This means all the user-defined function and all the other BC functions"]
        TermAlgebra(TermAlgebra<'bump>),
        #[doc="The `ite` from smt"]
        IfThenElse(IfThenElse),
        #[doc="To cast from term algebra to the evaluated space"]
        Evaluate(Evaluate<'bump>),
        #[doc="Other predicates"]
        Predicate(Predicate<'bump>),
        #[doc="When you need to define a function but not use it"]
        Tmp(Tmp<'bump>),
        Skolem(Skolem<'bump>),
        // #[doc="A function to be overwritten soon"]
        // Invalid(InvalidFunction),
    }
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

// impl<'bump> AsRef<InnerFunction<'bump>> for Function<'bump> {
//     fn as_ref(&self) -> &InnerFunction<'bump> {
//         self.precise_as_ref()
//     }
// }

// impl From<&Step> for Function {
//     fn from(s: &Step) -> Self {
//         s.function().clone()
//     }
// }

// impl<'bump> MaybeInvalid for InnerFunction<'bump> {
//     fn is_valid(&self) -> bool {
//     }
// }
