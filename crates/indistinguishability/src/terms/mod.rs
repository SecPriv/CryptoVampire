use egg::{Symbol, Var};

use crate::{Lang, LangVar};

// =========================================================
// ======================= macros ==========================
// =========================================================

/// helper to write flags
macro_rules! const_fun_flags {
    ($id:ident) => {$crate::terms::FunctionFlags::$id};
    ($id0:ident | $($id:ident)|*) => {
        $crate::terms::FunctionFlags::$id0
            $(.union($crate::terms::FunctionFlags::$id))*
    };
}

/// Shortcut for `Cow<'smt, [U]>`
macro_rules! cow {
    ($l:lifetime; $t:ty) => {
        ::std::borrow::Cow<$l, [$t]>
    };
    ($t:ty) => {
        ::std::borrow::Cow<'static, [$t]>
    };
}

/// Shortcut for `Cow<'smt, [U]>`
macro_rules! cowarc {
    ($l:lifetime; $t:ty) => {
        ::quarck::CowArc<$l, [$t]>
    };
    ($t:ty) => {
        ::quarck::CowArc<'static, [$t]>
    };
}

/// equivalent of [vec!] for [cow!] types
macro_rules! mk_cowarc {
    (@ $v:expr) => {
        ::quarck::CowArc::Owned($v)
    };
    () => {
        ::quarck::CowArc::Borrowed(&[])
    };
    ($($tt:tt)*) => {
        ::quarck::CowArc::Owned(::std::vec![$($tt)*].into())
    }
}

/// equivalent of [vec!] for [cow!] types
macro_rules! mk_cow {
    (@ $v:expr) => {
        ::std::borrow::Cow::Owned($v)
    };
    () => {
        ::std::borrow::Cow::Borrowed(&[])
    };
    ($($tt:tt)*) => {
        ::std::borrow::Cow::Owned(::std::vec![$($tt)*])
    }
}

/// helper to write owned signatures
#[macro_export]
macro_rules! mk_signature {
    (() -> $out:expr) => {
        {
            #[allow(unused_imports)]
            use $crate::terms::Sort::*;
            $crate::terms::Signature {
                inputs: std::borrow::Cow::Owned(vec![]),
                output: $out
            }
        }
    };
    ($t:expr, $n:literal) => {
        {
            #[allow(unused_imports)]
            use $crate::terms::Sort::*;
            $crate::terms::Signature {
                inputs: std::borrow::Cow::Owned(vec![$t; $n]),
                output: $t,
            }
        }
    };
    (($($ins:expr),*) -> $out:expr) => {
        {
            #[allow(unused_imports)]
            use $crate::terms::Sort::*;
            $crate::terms::Signature {
                inputs: std::borrow::Cow::Owned(vec![$($ins),*]),
                output: $out
            }
        }
    };
}

// =========================================================
// ======================= modules =========================
// =========================================================

mod functions_holder;
pub use functions_holder::*;

pub(crate) mod flags;
pub use flags::FunctionFlags;

mod formula;
pub(crate) use formula::InnerLang;
pub use formula::{FOBinder, RecFOFormula, RecExprIter, FormulaLike};

pub mod utils;

mod rewrite;
pub use rewrite::Rewrite;

mod alias;
pub use alias::{Alias, AliasRewrite};
pub use quantifier::*;
mod quantifier;

mod sort;
pub use sort::*;

mod signature;
pub use signature::*;

mod function;
pub use builtin::*;
pub use function::*;
mod builtin;

pub use cryptography::*;
mod cryptography;

pub(crate) mod variable;
pub use variable::Variable;

// =========================================================
// ======================== other ==========================
// =========================================================

pub type CowExpr = cow![Lang];
pub type CowPattern = cow![LangVar];