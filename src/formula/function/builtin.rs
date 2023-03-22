use static_init::dynamic;

use super::{
    booleans::{self, Booleans},
    new_static_function, Function, InnerFunction,
};

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
