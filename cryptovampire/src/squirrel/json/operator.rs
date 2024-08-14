use serde::{Deserialize, Serialize};

use super::*;

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum DhHyp {
    DH_DDH,
    DH_CDH,
    DH_GDH,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum Assoc {
    Right,
    Left,
    NonAssoc,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum SymbType {
    Prefix,
    Infix(Assoc),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum AbstractDef {
    Hash,
    DHgen(Vec<DhHyp>),
    AEnc,
    ADec,
    SEnc,
    SDec,
    Sign,
    CheckSign,
    PublicKey,
    Abstract(SymbType),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Concrete<'a> {
    #[serde(borrow)]
    pub name: Symb<'a>,
    #[serde(borrow)]
    pub type_variables: Vec<TypeVariable<'a>>,
    pub args: Vec<Variable<'a>>,
    pub out_type: Type<'a>,
    pub body: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(untagged)]
pub enum Def<'a> {
    Abstract {
        abstract_def: AbstractDef,
        #[serde(borrow)]
        associated_fun: Vec<Path<'a>>,
    },
    Concrete(Concrete<'a>),
}
// pub type DefaultDef<'a> = Def<'a>;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Data<'a> {
    #[serde(rename = "type", borrow)]
    pub sort: FunctionType<'a>,
    pub def: Def<'a>,
}
pub type Operator<'a> = Content<'a, operator::Data<'a>>;
