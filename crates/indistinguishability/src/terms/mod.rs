use std::{borrow::Cow, cmp::Ordering, fmt::Display, hash::Hash, ops::Deref, rc::Rc, sync::Arc};

use crate::{
    Lang, LangVar,
    protocol::{MacroKind, ProtocolLanguage},
};
use bitflags::bitflags_match;
use cryptovampire_smt::{SmtHead, SortedVar, VarInner};
use egg::{PatternAst, Symbol, SymbolLang, Var};
use itertools::izip;
use logic_formula::egg::{SimplLang, SimpleDiscriminant};
use serde::{Deserialize, Serialize};
use utils::{ereturn_if, implvec, match_eq, quack::CowArc};

mod functions_holder;
pub use functions_holder::*;

pub(crate) mod flags;
pub use flags::FunctionFlags;

mod unification;

mod first_order;
pub use first_order::{FOBinder, RecFOFormula};

pub mod formula_utils;

/// helper to write flags
macro_rules! const_fun_flags {
    ($id:ident) => {$crate::terms::FunctionFlags::$id};
    ($id0:ident | $($id:ident)|*) => {
        $crate::terms::FunctionFlags::$id0
            $(.union($crate::terms::FunctionFlags::$id))*
    };
}

macro_rules! cow {
    ($t:ty) => {
        ::std::borrow::Cow<'static, [$t]>
    };
}

pub type CowExpr = cow![Lang];
pub type CowPattern = cow![LangVar];

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct InnerFunction {
    pub name: Cow<'static, str>,
    pub signature: Signature,
    pub alias: Option<Alias>,
    pub flags: FunctionFlags,
    pub exists_idx: usize,
    pub protocol_idx: usize,
    pub step_idx: usize,
}

impl InnerFunction {
    pub const fn new(name: Cow<'static, str>, signature: Signature) -> Self {
        Self {
            name,
            signature,
            alias: None,
            flags: FunctionFlags::empty(),
            exists_idx: 0,
            protocol_idx: 0,
            step_idx: 0,
        }
    }
}

mod alias {
    use crate::terms::Sort;

    use super::{CowExpr, CowPattern};
    use serde::Serialize;

    /// When the fonction is an alias
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
    pub struct Alias(pub cow![AliasRewrite]);

    /// A rewrite rule for an alias
    #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
    pub struct AliasRewrite {
        /// These are the arguments to the function that one must unify with to get
        /// rewritten as [Self::to].
        pub from: cow![CowPattern],
        pub to: CowPattern,
        pub variables: cow![egg::Var],
        pub sorts: cow![Sort],
    }

    #[macro_export]
    macro_rules! mk_alias {
    ($( $($var:literal:$sort:ident),* in $($args:expr),* => $to:expr),*) => {
        {
            use $crate::terms::Sort::*;
            $crate::terms::Alias(::std::borrow::Cow::Owned(vec!
            [$($crate::terms::AliasRewrite {
                    from: ::std::borrow::Cow::Owned(vec![$($crate::terms::formula_utils::convert_to_cow($args)),*]),
                    to: $crate::terms::formula_utils::convert_to_cow($to),
                    variables: ::std::borrow::Cow::Owned(vec![$(::egg::Var::from_u32($var)),*]),
                    sorts: ::std::borrow::Cow::Owned(vec![$($sort),*]),
                }
            ),*]
            ))
        }
    };
}
}
pub use alias::{Alias, AliasRewrite};

// TODO: make comparison faster
/// Main type for function in this crate
///
/// This is basicaly a somewhat smart pointer to an [InnerFunction].
#[derive(Debug, Clone, Serialize, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Function(CowArc<'static, InnerFunction>);

#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Signature {
    pub inputs: cow![Sort],
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
    SubtermStatus,
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
    pub fn new(inputs: implvec!(Sort), output: Sort) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            output,
        }
    }

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

/// helper to write owned signatures
#[macro_export]
macro_rules! mk_signature {
    (() -> $out:expr) => {
        {
            use $crate::terms::Sort::*;
            $crate::terms::Signature {
                inputs: std::borrow::Cow::Owned(vec![]),
                output: $out
            }
    }
    };
    ($t:expr, $n:literal) => {
{
            use $crate::terms::Sort::*;
        $crate::terms::Signature {
            inputs: std::borrow::Cow::Owned(vec![$t; $n]),
            output: $t,
        }
 }
    };
  (($($ins:expr),*) -> $out:expr) => {
{
            use $crate::terms::Sort::*;
      $crate::terms::Signature {
        inputs: std::borrow::Cow::Owned(vec![$($ins),*]),
        output: $out
      }
 }
  };
}

impl Function {
    /// Build a [Function] from an inner reference.
    ///
    /// Mostly useful for the constants because this is `const`
    pub const fn from_ref(content: &'static InnerFunction) -> Self {
        Self(CowArc::from_ref(content))
    }

    pub fn new(inner: InnerFunction) -> Self {
        Self(CowArc::from(inner))
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
            FunctionFlags::EXISTS | FunctionFlags::SKOLEM | FunctionFlags::EXISTS_FRESH => Some(self.exists_idx),
            _ => None
        })
    }

    pub fn get_exists<'a>(&self, function: &'a FunctionCollection) -> Option<&'a Exists> {
        let idx = self.get_exist_index()?;
        function.quantifiers().get(idx)
    }

    pub fn get_protocol_index(&self) -> Option<usize> {
        self.is_protocol().then_some(self.protocol_idx)
    }

    pub fn get_step_index(&self) -> Option<usize> {
        self.is_step().then_some(self.step_idx)
    }

    pub fn get_alias(&self) -> Option<&Alias> {
        self.alias.as_ref()
    }

    pub fn as_smt_head(&self) -> Option<SmtHead> {
        use SmtHead::*;
        use builtin::*;
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

    pub fn rapp(&self, args: implvec!(RecFOFormula)) -> RecFOFormula {
        RecFOFormula::app(self.clone(), args.into_iter().collect())
    }

    // =========================================================
    // ==================== is functions =======================
    // =========================================================

    #[inline]
    pub fn is_should_not_declare_in_smt(&self) -> bool {
        static SHOULD_NOT_DECLARE_IN_SMT: FunctionFlags =
            const_fun_flags!(PROLOG_ONLY | BUILTIN_SMT);

        self.flags.intersects(SHOULD_NOT_DECLARE_IN_SMT)
    }

    #[inline]
    pub fn is_special_subterm(&self) -> bool {
        static SPECIAL_SUBTERM: FunctionFlags = const_fun_flags!(
            PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_SUBTERM | EXISTS | SKOLEM | SMT_ONLY
        );

        self.flags.intersects(SPECIAL_SUBTERM) || self.is_protocol() || self.is_alias()
    }

    #[inline]
    pub fn is_special_deduce(&self) -> bool {
        static SPECIAL_DEDUCE: FunctionFlags = const_fun_flags!(
            PROLOG_ONLY | MACRO | UNFOLD | CUSTOM_DEDUCE | EXISTS | SKOLEM | NONCE | SMT_ONLY
        );
        self.flags.intersects(SPECIAL_DEDUCE) || self.is_alias()
    }

    #[inline]
    pub fn is_protocol(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::PROTOCOL), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Protocol);
        true
    }

    #[inline]
    pub fn is_alias(&self) -> bool {
        self.get_alias().is_some()
    }

    #[inline]
    pub fn is_step(&self) -> bool {
        ereturn_if!(!self.flags.contains(FunctionFlags::STEP), false);
        // will return true
        assert_eq!(self.signature.output, Sort::Time);
        true
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

// impl Eq for Function {}

// impl PartialEq for Function {
//     fn eq(&self, other: &Self) -> bool {
//         match (&self.0, &other.0) {
//             (CowArc::Owned(a), CowArc::Owned(b)) => Arc::ptr_eq(a, b),
//             (CowArc::Borrowed(a), CowArc::Borrowed(b)) => ::core::ptr::eq(a, b),
//             _ => false,
//         }
//     }
// }

// impl PartialOrd for Function {
//     fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
//         if self == other {
//             // equality if defined by pointer
//             Some(Ordering::Equal)
//         } else {
//             // order by the content
//             match InnerFunction::cmp(self, other) {
//                 Ordering::Equal => None,
//                 x => Some(x),
//             }
//         }
//     }
// }

// impl Ord for Function {
//     fn cmp(&self, other: &Self) -> Ordering {
//         Self::partial_cmp(self, other).expect(
//             "duplicate function at two different location in memory! (The \
//             comparison algorithm is unsound in those cases, please avoid \
//             declaring function twice)",
//         )
//     }
// }

// impl Hash for Function {
//     fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
//         match &self.0 {
//             CowArc::Owned(x) => Arc::as_ptr(x),
//             CowArc::Borrowed(x) => *x as *const _,
//         }
//         .hash(state);
//     }
// }

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

pub fn convert_smt_var(var: cryptovampire_smt::VarInner) -> egg::Var {
    match var {
        VarInner::Int(x) => Var::from_u32(x),
        VarInner::Str(cow) => Var::from_symbol(Symbol::from(cow.as_ref())),
    }
}

// ~~~~~~~~~~~~~~~~ magic ~~~~~~~~~~~~~~~~~~~

pub use builtin::*;
mod builtin;
