use std::sync::Arc;

use static_init::dynamic;

use crate::container::StaticContainer;
use crate::formula::sort::builtins::{BITSTRING, MESSAGE};
use crate::formula::{formula::RichFormula, sort::builtins::STEP};

use super::inner::evaluate::Evaluate;

use super::inner::term_algebra::base_function::BaseFunctionTuple;
use super::inner::term_algebra::name_caster::NameCaster;
use super::inner::term_algebra::{self, TermAlgebra};
use super::{new_static_function, Function, InnerFunction};

use super::inner::{
    booleans::{self, Booleans},
    if_then_else::IfThenElse,
    predicate::Predicate,
};

macro_rules! builtin {
    ($($name:ident),* $(,)?) => {
        const __BUILT_IN_FUNCTION_LENGTH : usize = builtin!(@count $($name,)*);

        #[dynamic]
        pub static BUILT_IN_FUNCTIONS: [Function<'static>; __BUILT_IN_FUNCTION_LENGTH]
            = [$($name.clone()),*];
    };

    (@count ) => {0};

    (@count $a:tt, $($b:tt,)*) => {
        1 + builtin!(@count $($b,)*)
    };

}

#[dynamic]
pub static TRUE_F: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::True),
));

#[dynamic]
pub static TRUE_F_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::True,
    )),
));

#[dynamic]
pub static FALSE_F: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::False),
));

#[dynamic]
pub static FALSE_F_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::False,
    )),
));

#[dynamic]
pub static TRUE: RichFormula<'static> = RichFormula::Fun(TRUE_F.clone(), Arc::new([]));

#[dynamic]
pub static FALSE: RichFormula<'static> = RichFormula::Fun(TRUE_F.clone(), Arc::new([]));

#[dynamic]
pub static AND: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::And,
)));

#[dynamic]
pub static AND_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::And,
    )),
));

#[dynamic]
pub static OR: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Or,
)));

#[dynamic]
pub static OR_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::Or,
    )),
));

#[dynamic]
pub static NOT: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Not,
)));

#[dynamic]
pub static NOT_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::Not,
    )),
));

#[dynamic]
pub static IMPLIES: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::Implies),
));

#[dynamic]
pub static IMPLIES_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::Implies,
    )),
));

#[dynamic]
pub static IFF: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Iff,
)));

#[dynamic]
pub static IFF_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Condition(term_algebra::connective::Connective::BaseConnective(
        term_algebra::connective::BaseConnective::Iff,
    )),
));

#[dynamic]
pub static EQUALITY: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Equality(booleans::Equality()),
));

#[dynamic]
pub static EQUALITY_TA: Function<'static> =
    new_static_function(InnerFunction::TermAlgebra(TermAlgebra::Condition(
        term_algebra::connective::Connective::Equality(Default::default()),
    )));

#[dynamic]
pub static IF_THEN_ELSE: Function<'static> =
    new_static_function(InnerFunction::IfThenElse(IfThenElse));

#[dynamic]
pub static LESS_THAN_STEP: Function<'static> =
    new_static_function(InnerFunction::Predicate(Predicate {
        name: "lt".into(),
        args: Box::new([STEP.clone(), STEP.clone()]),
        // out: BOOL.clone(),
    }));

#[dynamic]
pub static HAPPENS: Function<'static> = new_static_function(InnerFunction::Predicate(Predicate {
    name: "happens".into(),
    args: Box::new([STEP.clone()]),
    // out: BOOL.clone(),
}));

#[dynamic]
pub static IF_THEN_ELSE_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    super::inner::term_algebra::TermAlgebra::IfThenElse(Default::default()),
));

#[dynamic]
pub static INPUT: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    super::inner::term_algebra::TermAlgebra::Input(Default::default()),
));

#[dynamic]
pub static NAME_TO_MESSAGE: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::NameCaster(NameCaster::new(MESSAGE.as_sort())),
));

#[dynamic]
pub static MESSAGE_TO_BITSTRING: Function<'static> =
    new_static_function(InnerFunction::Evaluate(Evaluate::new(
        "evaluate_msg".into(),
        MESSAGE.as_sort(),
        BITSTRING.as_sort(),
    )));

#[dynamic]
pub static CONDITION_TO_BOOL: Function<'static> =
    new_static_function(InnerFunction::Evaluate(Evaluate::new(
        "evaluate_cond".into(),
        MESSAGE.as_sort(),
        BITSTRING.as_sort(),
    )));

#[dynamic]
static EMPTY_TUPLE_FUNCTION: BaseFunctionTuple<'static> =
    Function::new_user_term_algebra(&StaticContainer, "empty", [], MESSAGE.clone());

#[dynamic]
pub static EMPTY: Function<'static> = (&EMPTY_TUPLE_FUNCTION).main.clone();

#[dynamic]
pub static EMPTY_EVALUATED: Function<'static> = (&EMPTY_TUPLE_FUNCTION).eval.clone();

builtin!(
    AND,
    AND_TA,
    EMPTY,
    EMPTY_EVALUATED,
    EQUALITY,
    EQUALITY_TA,
    FALSE_F,
    FALSE_F_TA,
    TRUE_F,
    TRUE_F_TA,
    HAPPENS,
    IF_THEN_ELSE,
    IF_THEN_ELSE_TA,
    IFF,
    IFF_TA,
    IMPLIES,
    IMPLIES_TA,
    INPUT,
    LESS_THAN_STEP,
    MESSAGE_TO_BITSTRING,
    NAME_TO_MESSAGE,
    NOT,
    NOT_TA,
    OR,
    OR_TA,
);
