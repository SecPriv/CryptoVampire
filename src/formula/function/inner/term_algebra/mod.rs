use crate::{
    assert_variance, formula::function::traits::FixedSignature, match_as_trait,
    utils::string_ref::StrRef, variants, CustomDerive,
};

use self::{
    base_function::BaseFunction,
    cell::Cell,
    connective::Connective,
    if_then_else::IfThenElse,
    input::Input,
    name::{Name, NameCaster},
    quantifier::Quantifier,
};

pub mod base_function;
pub mod cell;
pub mod connective;
pub mod if_then_else;
pub mod input;
pub mod name;
pub mod quantifier;

use macro_attr::*;

macro_attr! {
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone,
        CustomDerive!(maybe_evaluate, 'bump),
        CustomDerive!(fixed_signature, 'bump),
    )]
    pub enum TermAlgebra<'bump> {
        Condition(Connective),
        Quantifier(Quantifier<'bump>),
        Function(BaseFunction<'bump>),
        Cell(Cell<'bump>),
        Name(Name<'bump>),
        NameCaster(NameCaster<'bump>),
        Input(Input),
        IfThenElse(IfThenElse),
    }
}

impl<'bump> TermAlgebra<'bump> {
    pub fn is_default_subterm(&self) -> bool {
        match self {
            TermAlgebra::Condition(_)
            | TermAlgebra::Function(_)
            | TermAlgebra::IfThenElse(_)
            | TermAlgebra::NameCaster(_)
            | TermAlgebra::Name(_) => true,
            TermAlgebra::Quantifier(_) | TermAlgebra::Cell(_) | TermAlgebra::Input(_) => false,
        }
    }

    pub fn name(&self) -> StrRef<'_> {
        match_as_trait!(self => {
            TermAlgebra::Quantifier(x)
                | TermAlgebra::NameCaster(x)
                | TermAlgebra::Function(x)
                    => {x.name()},
            TermAlgebra::Condition(x)
                | TermAlgebra::Cell(x)
                | TermAlgebra::Name(x)
                | TermAlgebra::Input(x)
                | TermAlgebra::IfThenElse(x)
                    => {x.name().into()}
        })
    }

    // pub fn signature(&self) -> impl Signature<'bump> + '_ {
    //     match_as_trait!(self => {
    //         Self::Condition(x) => {Lazy::A(x.signature())},
    //         Self::Function(x)
    //             | Self::IfThenElse(x)
    //             | Self::NameCaster(x)
    //             | Self::Name(x)
    //             | Self::Quantifier(x)
    //             | Self::Cell(x)
    //             | Self::Input(x) => {Lazy::B(x.as_fixed_signature())}
    //     })
    // }

    variants!(TermAlgebra;
        Condition:Connective,
        Quantifier:Quantifier<'bump>,
        Function:BaseFunction<'bump>,
        Cell:Cell<'bump>,
        NameCaster:NameCaster<'bump>,
        Name:Name<'bump>);
}

assert_variance!(TermAlgebra);
