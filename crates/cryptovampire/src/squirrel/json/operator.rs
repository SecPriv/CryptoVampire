use serde::{Deserialize, Serialize};

use super::*;

#[allow(non_camel_case_types)]
#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum DhHyp {
    DH_DDH,
    DH_CDH,
    DH_GDH,
}

#[allow(clippy::enum_variant_names)]
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
        associated_fun: Vec<OperatorName<'a>>,
    },
    Concrete(Concrete<'a>),
}

impl<'a> Def<'a> {
    /// Returns `true` if the def is [`Concrete`].
    ///
    /// [`Concrete`]: Def::Concrete
    #[must_use]
    pub fn is_concrete(&self) -> bool {
        matches!(self, Self::Concrete(..))
    }

    #[must_use]
    pub fn as_concrete(&self) -> Option<&Concrete<'a>> {
        if let Self::Concrete(v) = self {
            Some(v)
        } else {
            None
        }
    }
}
// pub type DefaultDef<'a> = Def<'a>;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Data<'a> {
    #[serde(rename = "type", borrow)]
    pub sort: FunctionType<'a>,
    pub def: Def<'a>,
}

impl<'a> Data<'a> {
    pub fn def(&self) -> &Def<'a> {
        &self.def
    }
}
new_name!(OperatorName:Function);
pub type Operator<'a> = Content<OperatorName<'a>, operator::Data<'a>>;
