use std::fmt::{Debug, Display};

use logic_formula::Formula;
use serde::{Deserialize, Serialize};
use steel::rvals::IntoSteelVal;
use steel_derive::Steel;

use crate::Lang;
use crate::input::Registerable;
use crate::terms::formula::list;
use crate::terms::{BITSTRING_SORT, Function, INDEX_SORT, TIME_SORT};

#[non_exhaustive]
#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Steel, Default,
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
    pub fn unify(self, other: Self) -> bool {
        self.is_any() || other.is_any() || self == other
    }

    pub fn from_function(fun: &Function) -> Option<Self> {
        match fun {
            _ if fun == &BITSTRING_SORT => Some(Self::Bitstring),
            _ if fun == &INDEX_SORT => Some(Self::Index),
            _ if fun == &TIME_SORT => Some(Self::Time),
            _ => None,
        }
    }

    pub fn as_function(&self) -> Option<&'static Function> {
        match self {
            Sort::Bitstring => Some(&BITSTRING_SORT),
            Sort::Index => Some(&INDEX_SORT),
            Sort::Time => Some(&TIME_SORT),
            _ => None,
        }
    }

    /// see [sort_list::try_get_egraph]
    pub fn list_from_egg<N: egg::Analysis<Lang>>(
        egraph: &egg::EGraph<Lang, N>,
        f: egg::Id,
    ) -> Option<Vec<Sort>> {
        list::try_get_egraph(egraph, f)
    }

    pub fn list_from_formula<F>(f: F) -> Option<Vec<Sort>>
    where
        F: Formula,
        F::Fun: AsRef<Function>,
    {
        list::try_get(f)
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
            Sort::Any => write!(f, "Any"),
        }
    }
}

impl Debug for Sort {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
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
