use std::fmt::{Debug, Display};

use logic_formula::AsFormula;
use serde::{Deserialize, Serialize};
use steel::rvals::IntoSteelVal;
use steel_derive::Steel;

use crate::Lang;
use crate::input::Registerable;
use crate::terms::formula::list;
use crate::terms::{BITE, BITSTRING_SORT, Function, INDEX_SORT, MITE, TIME_SORT};

/// Represents the sort (type) of a term in the first-order logic.
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
    /// Returns `true` if the sort supports deduction (i.e., is `Bool` or `Bitstring`).
    pub const fn is_base(&self) -> bool {
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
    /// Checks if two sorts are unifiable, considering `Sort::Any` as a wildcard.
    #[inline]
    pub fn unify(self, other: Self) -> bool {
        self.is_any() || other.is_any() || self == other
    }

    /// Attempts to convert a `Function` into a `Sort`.
    ///
    /// This is used for functions that represent sorts themselves (e.g., `BITSTRING_SORT`).
    pub fn from_function(fun: &Function) -> Option<Self> {
        match fun {
            _ if fun == &BITSTRING_SORT => Some(Self::Bitstring),
            _ if fun == &INDEX_SORT => Some(Self::Index),
            _ if fun == &TIME_SORT => Some(Self::Time),
            _ => None,
        }
    }

    /// Returns the corresponding `Function` for the sort, if it has one.
    ///
    /// For example, `Sort::Bitstring` corresponds to `BITSTRING_SORT`.
    pub fn as_function(&self) -> Option<&'static Function> {
        match self {
            Sort::Bitstring => Some(&BITSTRING_SORT),
            Sort::Index => Some(&INDEX_SORT),
            Sort::Time => Some(&TIME_SORT),
            _ => None,
        }
    }

    /// see [sort_list::try_get_egraph]
    /// Extracts a list of sorts from an e-graph `Id`.
    ///
    /// This function is a wrapper around `list::try_get_egraph`.
    pub fn list_from_egg<N: egg::Analysis<Lang>>(
        egraph: &egg::EGraph<Lang, N>,
        f: egg::Id,
    ) -> Option<Vec<Sort>> {
        list::try_get_egraph(egraph, f)
    }

    /// Extracts a list of sorts from a `Formula`.
    ///
    /// This function is a wrapper around `list::try_get`.
    pub fn list_from_formula<F>(f: F) -> Option<Vec<Sort>>
    where
        F: AsFormula,
        F::Fun: AsRef<Function>,
    {
        list::try_get(f)
    }

    pub const fn short_name(&self) -> char {
        match self {
            Sort::Any => 'a',
            Sort::Bool => 'b',
            Sort::Bitstring => 'm',
            Sort::Time => 't',
            Sort::Protocol => 'p',
            Sort::Nonce => 'n',
            Sort::Index => 'i',
        }
    }

    pub const fn get_if(self) -> Option<Function> {
        match self {
            Self::Bool => Some(BITE.const_clone()),
            Self::Bitstring => Some(MITE.const_clone()),
            _ => None,
        }
    }
}

impl Display for Sort {
    /// Formats the `Sort` for display.
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
    /// Formats the `Sort` for debugging.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Registerable for Sort {
    /// Registers the `Sort` enum and its variants with the Steel VM.
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
