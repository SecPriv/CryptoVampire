use mtype::SortName;
use serde::{Deserialize, Serialize};

use super::*;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum Type<'a> {
    Message,
    Boolean,
    Index,
    Timestamp,
    // #[serde(rename_all = "PascalCase")]
    #[serde(borrow)]
    TBase(SortName<'a>),
    // #[serde(rename_all = "PascalCase")]
    TVar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    TUnivar {
        #[serde(flatten)]
        ident: Ident<'a>,
    },
    // #[serde(rename_all = "PascalCase")]
    Tuple {
        elements: Vec<Type<'a>>,
    },
    // #[serde(rename_all = "PascalCase")]
    Fun {
        #[serde(rename = "in")]
        t_in: Box<Type<'a>>,
        out: Box<Type<'a>>,
    },

    /// Isn't part of `squirrel` but greatly simplifies things
    Name,
}
