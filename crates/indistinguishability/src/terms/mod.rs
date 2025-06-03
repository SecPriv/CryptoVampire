use std::{borrow::Cow, cmp::Ordering, fmt::Display, hash::Hash, ops::Deref, rc::Rc, sync::Arc};

use crate::{
    protocol::{MacroKind, ProtocolLanguage},
    Lang,
};
use bitflags::{bitflags_match};
use cryptovampire_smt::{SmtHead, SortedVar, VarInner};
use egg::{PatternAst, SymbolLang, Var};
use itertools::izip;
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use serde::{Deserialize, Serialize};
use utils::{match_eq, quack::CowArc};

mod functions_holder;
pub use functions_holder::*;

pub(crate) mod flags;
pub use flags::FunctionFlags;

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub flags: FunctionFlags,
    exists_idx: usize,
}

/// Main type for function in this crate
///
/// This is basicaly a somewhat smart pointer to an [InnerFunction].
#[derive(Debug, Clone, Serialize)]
pub struct Function(CowArc<'static, InnerFunction>);

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Signature {
    pub inputs: Cow<'static, [Sort]>,
    pub output: Sort,
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Sort {
    Bool,
    Bitstring,
    Time,
    Protocol,
    Nonce,
    Index,

    // special
    SubtermStatus
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

pub use existential_quantifier::*;
mod existential_quantifier;

impl Signature {
    pub fn arity(&self) -> usize {
        self.inputs.len()
    }

    pub fn inputs_iter(&self) -> impl Iterator<Item = Sort> + use<'_> {
        self.inputs.iter().copied()
    }

    pub fn mk_sorted_vars(&self, from: u32) -> impl Iterator<Item = SortedVar<Sort>> + use<'_> {
        izip!(from.., self.inputs.iter()).map(|(i, s)| SortedVar {
            var: VarInner::Int(i),
            sort: *s,
        })
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

    /// static [Function] can be statically cloned. This function lets you do
    /// that. It returns [None] when the [Function] is not static
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

    pub fn as_smt_head(&self) -> Option<SmtHead> {
        use builtin::*;
        use SmtHead::*;
        match_eq! { self => {
            AND => { Some(And) },
            NOT => { Some(Not) },
            OR => { Some(Or) },
            IMPLIES => { Some(Implies) },
            EQ => { Some(Eq) },
            BITE | MITE => {Some(If)},
            TRUE => { Some(True) },
            FALSE => { Some(False) },
            _ => { None }
        }}
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

impl Eq for Function {}

impl PartialEq for Function {
    fn eq(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (CowArc::Owned(a), CowArc::Owned(b)) => Arc::ptr_eq(a, b),
            (CowArc::Borrowed(a), CowArc::Borrowed(b)) => ::core::ptr::eq(a, b),
            _ => false,
        }
    }
}

impl PartialOrd for Function {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Function::cmp(self, other))
    }
}

impl Ord for Function {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            // equality if defined by pointer
            Ordering::Equal
        } else {
            // order by the content
            match InnerFunction::cmp(self, other) {
                Ordering::Equal => panic!(
                    "duplicate function at two different location in memory! (The \
                    comparison algorithm is unsound in those cases, please avoid \
                    declaring function twice)"
                ),
                x => x,
            }
        }
    }
}

impl Hash for Function {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match &self.0 {
            CowArc::Owned(x) => Arc::as_ptr(x),
            CowArc::Borrowed(x) => *x as *const _,
        }
        .hash(state);
    }
}

// ~~~~~~~~~~~~ egg::Language ~~~~~~~~~~~~~~~

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

// ~~~~~~~~~~~~~~~~ magic ~~~~~~~~~~~~~~~~~~~

pub use builtin::*;
mod builtin;
