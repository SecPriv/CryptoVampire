macro_rules! s {
  ($($ins:ident),* -> $out:ident) => {
      Signature {
        inputs: Cow::Borrowed(&[$($ins),*]),
        output: $out
      }
  };
  (() -> $out:ident) => {
      Signature {
        inputs: Cow::Borrowed(&[]),
        output: $out
      }
  };
  }

macro_rules! b {
    ($t:ident, $n:literal) => {
        Signature {
            inputs: Cow::Borrowed(&[$t; $n]),
            output: $t,
        }
    };
}
macro_rules! n {
    ($n:literal) => {
        Cow::Borrowed($n)
    };
}
use cryptovampire_macros::mk_builtin_funs;
use egg::{Analysis, Rewrite};
use logic_formula::egg::SimplLang;

use crate::Configuration;

use super::{Function, FunctionFlags, InnerFunction, Signature, Sort::*};
use std::borrow::Cow;

static M_ALIAS: FunctionFlags = FunctionFlags::BUILTIN.union(FunctionFlags::ALIAS);

mk_builtin_funs!(
    // The "default" value.
    //
    // The field declared here will be copied in every struct, unless it is overwitten
    {
        flags: FunctionFlags::BUILTIN
    };

    // =========================================================
    // ===================== the structs =======================
    // =========================================================

    // bool

    BITE {
        signature: b!(Bool, 3),
        name: n!("bool_if_then_else")
    };

    IMPLIES {
        signature: b!(Bool, 2),
        name: n!("bit_implies"),
        flags: M_ALIAS // e.g., this will be `M_ALIAS` instead of `FunctionFlags::BUILTIN`
    };

    AND {
        signature: b!(Bool, 2),
        name: n!("bit_and"),
        flags: M_ALIAS
    };

    OR {
        signature: b!(Bool, 2),
        name: n!("bit_or"),
        flags: M_ALIAS
    };

    NOT {
        signature: b!(Bool, 1),
        name: n!("bit_not"),
        flags: M_ALIAS
    };

    EQ {
        signature: s!(Bitstring, Bitstring -> Bool),
        name: n!("meq"),
    };

    MITE {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        name: n!("bitstring_if_then_else"),
    };

    TRUE {
        signature: s!(() -> Bool),
        name: n!("m_true")
    };

    // ptcl

    HAPPENS {
        signature: s!(Time -> Bool),
        name: n!("happens"),
    };

    LT {
        signature: s!(Time, Time -> Bool),
        name: n!("lt"),
    };

    LEQ {
        signature: s!(Time, Time -> Bool),
        name: n!("leq"),
    };

    PRED {
        signature: b!(Time, 1),
        name: n!("pred"),
    };

    // macro

    ATT {
        signature: s!(Time -> Bitstring),
        name: n!("att"),
    };

    MACRO_INPUT {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("macro_input"),
    };

    MACRO_FRAME {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("macro_frame"),
    };

    MACRO_MSG {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("macro_msg"),
    };

    MACRO_COND {
        signature: s!(Time, Protocol -> Bool),
        name: n!("macro_cond"),
    };

    MACRO_EXEC {
        signature: s!(Time, Protocol -> Bool),
        name: n!("macro_exec"),
    };

    UNFOLD_INPUT {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("unfold_input"),
    };

    UNFOLD_FRAME {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("unfold_frame"),
    };

    UNFOLD_MSG {
        signature: s!(Time, Protocol -> Bitstring),
        name: n!("unfold_msg"),
    };

    UNFOLD_COND {
        signature: s!(Time, Protocol -> Bool),
        name: n!("unfold_cond"),
    };

    UNFOLD_EXEC {
        signature: s!(Time, Protocol -> Bool),
        name: n!("unfold_exec"),
    };


    // polog only

    GOAL {
        signature: s!(() -> Bitstring), // kinda irrelevant here
        name: n!("goal"),
        flags: FunctionFlags::BUILTIN.union(FunctionFlags::PROLOG_ONLY)
    }
);

pub fn mk_golgge_rewrites<const N: usize, A>(
    _config: &Configuration,
) -> impl Iterator<Item = Rewrite<SimplLang<Function, N>, A>>
where
    A: Analysis<SimplLang<Function, N>>,
{
    

    [].into_iter()
}
