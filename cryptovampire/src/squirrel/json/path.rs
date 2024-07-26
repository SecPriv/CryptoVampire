use super::{Symb, Type};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct NamesPath<'a> {
    #[serde(borrow)]
    npath: Vec<Symb<'a>>,
    // ignored field
    // id: u32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Path<'a> {
    #[serde(borrow)]
    npath: NamesPath<'a>,
    symb: Symb<'a>,
    // ignored field
    // id: u32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct ISymb<'a> {
    #[serde(borrow)]
    s_symb: Box<Path<'a>>,
    s_typ: Box<Type<'a>>,
}
