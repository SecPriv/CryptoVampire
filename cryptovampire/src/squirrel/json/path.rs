use std::fmt::Display;

use super::{Symb, Type};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use utils::string_ref::StrRef;

const SEPARATOR: &'static str = "$#$";

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Default)]
pub struct NamesPath<'a> {
    #[serde(borrow)]
    pub npath: Vec<Symb<'a>>,
    // ignored field
    // id: u32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Path<'a> {
    #[serde(borrow)]
    pub npath: NamesPath<'a>,
    pub symb: Symb<'a>,
    // ignored field
    // id: u32,
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct ISymb<'a> {
    #[serde(borrow)]
    pub s_symb: Box<Path<'a>>,
    pub s_typ: Box<Type<'a>>,
}

impl<'a> Display for Path<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.npath
                .npath
                .iter()
                .chain([&self.symb].into_iter())
                .format(SEPARATOR),
        )
    }
}

pub trait Pathed<'a> {
    fn path(&self) -> &Path<'a>;

    fn equiv_name_ref(&self) -> StrRef<'a> {
        self.path().to_string().into()
    }
}

impl<'a> Pathed<'a> for Path<'a> {
    fn path(&self) -> &Path<'a> {
        self
    }
}

impl<'a> Pathed<'a> for ISymb<'a> {
    fn path(&self) -> &Path<'a> {
        self.s_symb.as_ref()
    }
}

impl<'a> From<Symb<'a>> for Path<'a> {
    fn from(symb: Symb<'a>) -> Self {
        Self {
            npath: Default::default(),
            symb,
        }
    }
}
