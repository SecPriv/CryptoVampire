use serde::{Deserialize, Serialize};
use std::fmt::Display;
use steel::{rvals::IntoSteelVal, steel_vm::register_fn::RegisterFn};
use steel_derive::Steel;

use crate::input::Registerable;

#[non_exhaustive]
#[derive(
    Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Steel, Default
)]
#[steel(equality)]
pub enum Sort {
    /// for prolog
    #[default]
    Any,

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

    /// Returns `true` if the sort is [`Any`].
    ///
    /// [`Any`]: Sort::Any
    #[must_use]
    #[inline]
    pub const fn is_any(&self) -> bool {
        matches!(self, Self::Any)
    }

    /// Are the two sort equal modulo [Sort::Any] ?
    #[inline]
    pub fn unify(self, other:Self) -> bool {
        self.is_any() || other.is_any() || self == other
    }
}

impl Display for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sort::Bool => write!(f, "Bool"),
            Sort::Bitstring => write!(f, "Bitstring"),
            Sort::Time => write!(f, "Time"),
            Sort::Protocol => write!(f, "Protocol"),
            Sort::Nonce => write!(f, "Nonce"),
            Sort::Index => write!(f, "Index"),
            Sort::SubtermStatus => write!(f, "SubtermStatus"),
            Sort::Any => write!(f, "Any")
        }
    }
}

impl Registerable for Sort {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_enum_variants(module);
        module.register_type::<Self>("Sort?");
        use Sort::*;
        for v in [Bool, Bitstring, Time, Nonce, Index, Protocol] {
            let tmp = format!("{v}").leak();
            // module.register_fn(tmp, move || v);
            module.register_value(tmp, v.into_steelval().unwrap());
        }
        module
    }
}
