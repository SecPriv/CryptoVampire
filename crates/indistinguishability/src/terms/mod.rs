use std::{borrow::Cow, fmt::Display, ops::Deref, rc::Rc};

use crate::{protocol::{MacroKind, ProtocolLanguage}, Lang};
use bitflags::{bitflags, bitflags_match};
use egg::{PatternAst, SymbolLang, Var};
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use serde::{Deserialize, Serialize};
use utils::quack::CowArc;

mod functions_holder;
pub use functions_holder::*;

bitflags! {
    #[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Serialize, Deserialize)]
    pub struct FunctionFlags: u16 {
        const BUILTIN = 1 << 0;
        const ALIAS = 1 << 1;
        const PROLOG_ONLY = 1 << 2;

        const MACRO = 1 << 3;
        const UNFOLD = 1 << 4;

        const CUSTOM_DEDUCE = 1 << 5;

        const EXISTS = 1 << 6;
        const SKOLEM = 1 << 7;
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub flags: FunctionFlags,
    exists_idx: usize,
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
    Nonce
}

pub use quantifier::*;
mod quantifier;

impl Signature {
    pub fn arity(&self) -> usize {
        self.inputs.len()
    }

    pub fn inputs_iter(&self) -> impl Iterator<Item = Sort> + use<'_> {
        self.inputs.iter().copied()
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

    pub const fn const_clone(&self) -> Option<Self> {
        match self.0 {
            CowArc::Owned(_) => None,
            CowArc::Borrowed(x) => Some(Self::from_ref(x)),
        }
    }

    pub fn get_exist_index(&self) -> Option<usize> {
        bitflags_match!(self.flags,{
            FunctionFlags::EXISTS | FunctionFlags::SKOLEM => Some(self.exists_idx),
            _ => None
        })
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
