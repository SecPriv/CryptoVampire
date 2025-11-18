use crate::{Lang, LangVar};

// =========================================================
// ======================= macros ==========================
// =========================================================

/// A helper macro to create a `FunctionFlags` from a list of flags.
///
/// # Example
///
/// ```ignore
/// const_fun_flags!(STEP | PROTOCOL)
/// ```
macro_rules! const_fun_flags {
    ($id:ident) => {$crate::terms::FunctionFlags::$id};
    ($id0:ident | $($id:ident)|*) => {
        $crate::terms::FunctionFlags::$id0
            $(.union($crate::terms::FunctionFlags::$id))*
    };
}

/// A shortcut for `Cow<[T]>`.
macro_rules! cow {
    ($l:lifetime; $t:ty) => {
        ::std::borrow::Cow<$l, [$t]>
    };
    ($t:ty) => {
        ::std::borrow::Cow<'static, [$t]>
    };
}

/// A shortcut for `quarck::CowArc<[T]>`.
macro_rules! cowarc {
    ($l:lifetime; $t:ty) => {
        ::quarck::CowArc<$l, [$t]>
    };
    ($t:ty) => {
        ::quarck::CowArc<'static, [$t]>
    };
}

/// A macro to create a `quarck::CowArc<[T]>` from a list of elements.
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

/// A macro to create a `Cow<[T]>` from a list of elements.
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

/// A helper macro to create a `Signature`.
///
/// # Example
///
/// ```
/// # use indistinguishability::{mk_signature, terms::Sort};
/// mk_signature!((Sort::Bitstring, Sort::Bitstring) -> Sort::Bitstring);
/// ```
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
pub use formula::{
    AlphaArgs, FOBinder, Formula, FormulaLike, RecFOFormulaQuant, RecFOFormulaQuantRef,
    Substitution,
};
pub(crate) use formula::{InnerLang, QuantifierTranslator, list};

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

/// A `Cow` of `Lang`
pub type CowExpr = cow![Lang];
/// A `Cow` of `LangVar`
pub type CowPattern = cow![LangVar];
