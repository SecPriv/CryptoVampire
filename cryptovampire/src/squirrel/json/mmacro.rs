use super::*;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Data<'a> {
    General(#[serde(borrow)] GeneralMacro<'a>),
    Global(GlobalMacro<'a>),
    State(StateMacro<'a>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
#[serde(untagged)]
pub enum GeneralMacro<'a> {
    ProtocolMacro(ProtocolMacro),
    Structured(#[serde(borrow)] Structured<'a>),
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum ProtocolMacro {
    Output,
    Cond,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Structured<'a> {
    #[serde(borrow)]
    pub name: Path<'a>,
    pub default: Term<'a>,
    pub tinit: Term<'a>,
    pub body: StructuredBody<'a>,
    pub rec_ty: Type<'a>,
    pub ty: Type<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct StructuredBody<'a> {
    #[serde(borrow)]
    pub body: Term<'a>,
    pub var: Variable<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct GlobalMacro<'a> {
    pub arity: usize,
    #[serde(rename = "type", borrow)]
    pub sort: Type<'a>,
    pub data: GlobalData<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct StateMacro<'a> {
    pub arity: usize,
    #[serde(rename = "type", borrow)]
    pub sort: Type<'a>,
    pub init: StateMacroDef<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct StateMacroDef<'a> {
    #[serde(borrow)]
    pub vars: Vec<Variable<'a>>,
    pub init: Term<'a>,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct GlobalData<'a> {
    pub action: action::Action,
    #[serde(borrow)]
    pub inputs: Vec<Variable<'a>>,
    pub indices: Vec<Variable<'a>>,
    pub ts: Variable<'a>,
    pub ty: Type<'a>,
    pub body: Term<'a>,
}

pub mod action {
    use serde::{Deserialize, Serialize};

    use crate::squirrel::json::action;

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
    pub struct Action {
        pub kind: Kind,
        pub shape: action::Shape,
    }

    #[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
    pub enum Kind {
        Large,
        Strict,
    }
}
pub type Macro<'a> = Content<'a, mmacro::Data<'a>>;
pub type MacroRef<'a, 'b> = ContentRef<'a, 'b, mmacro::Data<'a>>;
