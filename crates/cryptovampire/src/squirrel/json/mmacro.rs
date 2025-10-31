use serde::{Deserialize, Serialize};

use super::*;

new_name!(MacroName:Macro);

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Data<'a> {
    General(#[serde(borrow)] GeneralMacro<'a>),
    Global(GlobalMacro<'a>),
    State(StateMacro<'a>),
}

impl<'a> Data<'a> {
    pub fn inputs<'b>(&'b self) -> impl DoubleEndedIterator<Item = &'b Variable<'a>> {
        match self {
            Data::Global(gm) => Some(gm.inputs()),
            _ => None,
        }
        .into_iter()
        .flatten()
    }
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

impl<'a> GlobalMacro<'a> {
    pub fn inputs<'b>(&'b self) -> impl DoubleEndedIterator<Item = &'b Variable<'a>> {
        self.data.inputs()
    }
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

impl<'a> GlobalData<'a> {
    pub fn inputs<'b>(&'b self) -> impl DoubleEndedIterator<Item = &'b Variable<'a>> {
        self.inputs.iter().filter(|v| !v.is_dummy())
    }
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

pub type Macro<'a> = Content<MacroName<'a>, Data<'a>>;
pub type MacroRef<'a, 'b> = ContentRef<'b, MacroName<'a>, Data<'a>>;
