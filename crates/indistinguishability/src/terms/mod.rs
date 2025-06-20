use crate::{Lang, LangVar};
use cryptovampire_smt::VarInner;
use egg::{Symbol, Var};

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

macro_rules! cow {
    ($t:ty) => {
        ::std::borrow::Cow<'static, [$t]>
    };
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

// =========================================================
// ======================= modules =========================
// =========================================================

mod functions_holder;
pub use functions_holder::*;

pub(crate) mod flags;
pub use flags::FunctionFlags;

mod unification;

mod first_order;
pub use first_order::{FOBinder, RecFOFormula};

pub mod formula_utils;

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
pub use function::*;

pub use builtin::*;
mod builtin;

// =========================================================
// ======================== other ==========================
// =========================================================

pub type CowExpr = cow![Lang];
pub type CowPattern = cow![LangVar];

pub fn convert_smt_var(var: cryptovampire_smt::VarInner) -> Var {
    match var {
        VarInner::Int(x) => Var::from_u32(x),
        VarInner::Str(cow) => Var::from_symbol(Symbol::from(cow.as_ref())),
    }
}
