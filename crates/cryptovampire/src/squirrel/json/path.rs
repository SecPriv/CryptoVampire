use std::fmt::Display;

use itertools::Itertools;
use serde::{Deserialize, Serialize};
use utils::string_ref::StrRef;

use super::{Symb, Type};
use crate::squirrel::{Sanitizable, SanitizeKind};

const SEPARATOR: &str = "$#$";

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Default)]
pub struct NamesPath<'a> {
    #[serde(borrow)]
    pub npath: Vec<Symb<'a>>,
    // ignored field
    // id: u32,
}

impl<'a, 'b> Sanitizable<'b> for NamesPath<'a> {
    fn to_str_ref(&self) -> StrRef<'b> {
        self.npath.iter().map(|s| s.as_str()).join(SEPARATOR).into()
    }

    fn sanitize_kind(&self) -> SanitizeKind {
        SanitizeKind::Name
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Path<'a> {
    #[serde(borrow)]
    pub npath: NamesPath<'a>,
    pub symb: Symb<'a>,
    // ignored field
    // id: u32,
}

impl<'a> Path<'a> {
    pub fn input() -> Self {
        Self {
            npath: NamesPath { npath: vec![] },
            symb: "input".into(),
        }
    }

    pub fn to_str_ref(&self) -> StrRef<'a> {
        if self.npath.npath.is_empty() {
            self.symb.clone().drop_guard()
        } else {
            self.to_string().into()
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct ISymb<'a> {
    #[serde(borrow)]
    pub s_symb: Box<Path<'a>>,
    pub s_typ: Box<Type<'a>>,
}

impl<'a> ISymb<'a> {
    pub fn input() -> Self {
        Self {
            s_symb: Box::new(Path::input()),
            s_typ: Box::new(Type::Message),
        }
    }

    pub fn path(&self) -> &Path<'a> {
        &self.s_symb
    }
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

impl<'a> From<Symb<'a>> for Path<'a> {
    fn from(symb: Symb<'a>) -> Self {
        Self {
            npath: Default::default(),
            symb,
        }
    }
}
