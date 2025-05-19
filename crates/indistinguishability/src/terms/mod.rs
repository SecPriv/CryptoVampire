use std::{borrow::Cow, fmt::Display, ops::Deref, rc::Rc};

use bitflags::bitflags;
use egg::SymbolLang;
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use serde::{Deserialize, Serialize};
use utils::quack::CowArc;
use crate::protocol::{MacroKind, ProtocolLanguage};

bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
    pub struct FunctionFlags: u8 {
        const BUILTIN = 1 << 0;
        const ALIAS = 1 << 1;
        const PROLOG_ONLY = 1 << 2;
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub flags: FunctionFlags,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Function(CowArc<'static, InnerFunction>);

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Signature {
    pub inputs: Cow<'static, [Sort]>,
    pub output: Sort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sort {
    Bool,
    Bitstring,
    Time,
    Protocol,
}

impl Signature {
    pub fn arity(&self) -> usize {
        self.inputs.len()
    }
}

impl Function {
    /// Build a [Function] from an inner reference.
    ///
    /// Mostly useful for the constants because this is `const`
    pub const fn from_ref(content: &'static InnerFunction) -> Self {
        Self(CowArc::from_ref(content))
    }

    /// The arity of the function
    ///
    /// [egg::RecExpr] are check at build time, so that all functions have the right arity
    pub fn arity(&self) -> usize {
        self.signature.arity()
    }

    /// Get the `macro` function from a [MacroKind]
    pub const fn macro_from_kind(kind: MacroKind) -> &'static Self {
        match kind {
            MacroKind::Frame => &MACRO_FRAME,
            MacroKind::Input => &MACRO_INPUT,
            MacroKind::Cond => &MACRO_COND,
            MacroKind::Msg => &MACRO_MSG,
            MacroKind::Exec => &MACRO_EXEC,
        }
    }

    /// Get the `unfold` function from a [MacroKind]
    pub const fn unfold_from_kind(kind: MacroKind) -> &'static Self {
        match kind {
            MacroKind::Frame => &UNFOLD_FRAME,
            MacroKind::Input => &UNFOLD_INPUT,
            MacroKind::Cond => &UNFOLD_COND,
            MacroKind::Msg => &UNFOLD_MSG,
            MacroKind::Exec => &UNFOLD_EXEC,
        }
    }
}

impl Display for Function {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.name.fmt(f)
    }
}

impl Deref for Function {
    type Target = InnerFunction;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl SimpleDiscriminant for Function {
    fn valid(&self, ids: &[egg::Id]) -> bool {
        self.arity() == ids.len()
    }
}

impl<const N: usize> ProtocolLanguage for SimplLang<Function, N> {
    fn mk_happens(step: egg::Id) -> Self {
        HAPPENS.app_id([step])
    }

    fn mk_true() -> Self {
        TRUE.app_id([])
    }

    fn mk_macro(kind: MacroKind, step: egg::Id, ptcl: egg::Id) -> Self {
        Function::macro_from_kind(kind).app_id([step, ptcl])
    }

    fn mk_unfold(kind: MacroKind, step: egg::Id, ptcl: egg::Id) -> Self {
        Function::unfold_from_kind(kind).app_id([step, ptcl])
    }
}

pub use builtin::*;
mod builtin;