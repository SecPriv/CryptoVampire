use serde::{Deserialize, Serialize};
use std::fmt::Display;
use steel_derive::Steel;

use crate::input::Registerable;

#[non_exhaustive]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Steel,
)]
pub enum Sort {
    Bool,
    Bitstring,
    Time,
    Protocol,
    Nonce,
    Index,

    // special
    SubtermStatus,
}

impl Sort {
    pub const fn support_deduce(&self) -> bool {
        matches!(self, Self::Bool | Self::Bitstring)
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Bitstring => write!(f, "Bitstring"),
            Sort::Time => write!(f, "Time"),
            Sort::Protocol => write!(f, "Procotol"),
            Sort::Nonce => write!(f, "Nonce"),
            Sort::Index => write!(f, "Index"),
            Sort::SubtermStatus => write!(f, "SubtermStatus"),
        }
    }
}

impl Registerable for Sort {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_enum_variants(module)
    }
}
