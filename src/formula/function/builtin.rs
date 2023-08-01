use static_init::dynamic;

use crate::formula::{formula::RichFormula, sort::builtins::STEP};

use super::{new_static_function, Function, InnerFunction};

use super::inner::{
    booleans::{self, Booleans},
    if_then_else::IfThenElse,
    predicate::Predicate,
};

#[dynamic]
pub static TRUE_F: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::True),
));

#[dynamic]
pub static FALSE_F: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::False),
));

#[dynamic]
pub static TRUE: RichFormula<'static> = RichFormula::Fun(TRUE_F.clone(), vec![]);

#[dynamic]
pub static FALSE: RichFormula<'static> = RichFormula::Fun(TRUE_F.clone(), vec![]);

#[dynamic]
pub static AND: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::And,
)));

#[dynamic]
pub static OR: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Or,
)));

#[dynamic]
pub static NOT: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Not,
)));

#[dynamic]
pub static IMPLIES: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Connective(booleans::Connective::Implies),
));

#[dynamic]
pub static IFF: Function<'static> = new_static_function(InnerFunction::Bool(Booleans::Connective(
    booleans::Connective::Iff,
)));

#[dynamic]
pub static EQUALITY: Function<'static> = new_static_function(InnerFunction::Bool(
    Booleans::Equality(booleans::Equality()),
));

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
