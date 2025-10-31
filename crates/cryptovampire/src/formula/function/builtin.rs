use std::sync::Arc;

use static_init::dynamic;

use super::inner::booleans::{self, Booleans};
use super::inner::evaluate::Evaluate;
use super::inner::if_then_else::IfThenElse;
use super::inner::predicate::Predicate;
use super::inner::step::StepFunction;
use super::inner::term_algebra::base_function::BaseFunctionTuple;
use super::inner::term_algebra::name_caster::NameCaster;
use super::inner::term_algebra::step_macro::Macro;
use super::inner::term_algebra::{self, TermAlgebra};
use super::{Function, InnerFunction, new_static_function};
use crate::container::StaticContainer;
use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::sort::builtins::{BITSTRING, BOOL, CONDITION, MESSAGE, STEP};

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
pub static TRUE: RichFormula<'static> = RichFormula::Fun(*TRUE_F, Arc::new([]));

#[dynamic]
pub static TRUE_ARC: ARichFormula<'static> = TRUE.clone_as_arc();

#[dynamic]
pub static FALSE: RichFormula<'static> = RichFormula::Fun(*TRUE_F, Arc::new([]));

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

// #[dynamic]
// pub static IFF: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
//     booleans::Connective::Iff,
// )));

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
        args: Box::new([*STEP, *STEP]),
        // out: BOOL.clone(),
    }));

#[dynamic]
pub static GREATER_THAN_STEP: Function<'static> =
    new_static_function(InnerFunction::Predicate(Predicate {
        name: "gt".into(),
        args: Box::new([*STEP, *STEP]),
        // out: BOOL.clone(),
    }));

#[dynamic]
pub static LESS_THAN_EQ_STEP: Function<'static> =
    new_static_function(InnerFunction::Predicate(Predicate {
        name: "leq".into(),
        args: Box::new([*STEP, *STEP]),
        // out: BOOL.clone(),
    }));

#[dynamic]
pub static HAPPENS: Function<'static> = new_static_function(InnerFunction::Predicate(Predicate {
    name: "happens".into(),
    args: Box::new([*STEP]),
    // out: BOOL.clone(),
}));

#[dynamic]
pub static IF_THEN_ELSE_TA: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    super::inner::term_algebra::TermAlgebra::IfThenElse(Default::default()),
));

#[dynamic]
pub static INPUT: Function<'static> = {
    use super::inner::term_algebra;
    new_static_function(InnerFunction::TermAlgebra(
        term_algebra::TermAlgebra::Macro(term_algebra::step_macro::Macro::Input),
    ))
};

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
pub static CONDITION_TO_BOOL: Function<'static> = new_static_function(InnerFunction::Evaluate(
    Evaluate::new("evaluate_cond".into(), CONDITION.as_sort(), BOOL.as_sort()),
));

pub const EMPTY_FUN_NAME: &str = "empty";

#[dynamic]
static EMPTY_TUPLE_FUNCTION: BaseFunctionTuple<'static> =
    Function::new_user_term_algebra(&StaticContainer, EMPTY_FUN_NAME, [], *MESSAGE);

#[dynamic]
pub static EMPTY: Function<'static> = EMPTY_TUPLE_FUNCTION.main;

#[dynamic]
pub static PRED: Function<'static> =
    new_static_function(InnerFunction::Step(StepFunction::Pred(Default::default())));

#[dynamic]
pub static CONDITION_MACRO: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Macro(Macro::Condition),
));

#[dynamic]
pub static MESSAGE_MACRO: Function<'static> = new_static_function(InnerFunction::TermAlgebra(
    TermAlgebra::Macro(Macro::Message),
));

#[dynamic]
pub static EXEC_MACRO: Function<'static> =
    new_static_function(InnerFunction::TermAlgebra(TermAlgebra::Macro(Macro::Exec)));

builtin!(
    AND,
    AND_TA,
    EMPTY,
    // EMPTY_EVALUATED,
    EQUALITY,
    EQUALITY_TA,
    FALSE_F,
    FALSE_F_TA,
    TRUE_F,
    TRUE_F_TA,
    HAPPENS,
    IF_THEN_ELSE,
    IF_THEN_ELSE_TA,
    // IFF,
    IFF_TA,
    IMPLIES,
    IMPLIES_TA,
    INPUT,
    LESS_THAN_STEP,
    GREATER_THAN_STEP,
    LESS_THAN_EQ_STEP,
    NAME_TO_MESSAGE,
    NOT,
    NOT_TA,
    OR,
    OR_TA,
    PRED,
    CONDITION_MACRO,
    MESSAGE_MACRO,
    EXEC_MACRO
);
