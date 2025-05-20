use super::{Function, FunctionFlags, InnerFunction, Signature, Sort::*};
use cryptovampire_macros::mk_builtin_funs;
use std::borrow::Cow;

/// helper to write signatures
macro_rules! s {
    ($t:ident, $n:literal) => {
        Signature {
            inputs: Cow::Borrowed(&[$t; $n]),
            output: $t,
        }
    };
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

/// helper to write flags
macro_rules! f {
    ($($id:ident)|*) => {
        FunctionFlags::BUILTIN
            $(.union(FunctionFlags::$id))*
    };
}

mk_builtin_funs!(
    // The "default" value.
    //
    // The field declared here will be copied in every struct, unless it is overwitten
    {
        flags: FunctionFlags::BUILTIN,
        exists_idx: 0
    };

    // =========================================================
    // ===================== the structs =======================
    // =========================================================

    // bool

    BITE "bool_if_then_else" "b_ite" {
        signature: s!(Bool, 3),
        flags: f!(CUSTOM_DEDUCE)
    };

    IMPLIES "bit_implies" "implies" "=>" "mimplies" {
        signature: s!(Bool, 2),
        flags: f!(ALIAS) // e.g., this will be `M_ALIAS` instead of `FunctionFlags::BUILTIN`
    };

    AND "bit_and" "and" "mand" {
        signature: s!(Bool, 2),
        flags: f!(ALIAS)
    };

    OR "bit_or" "or" "mor" {
        signature: s!(Bool, 2),
        flags: f!(ALIAS)
    };

    NOT "bit_not" "not" "mnot" {
        signature: s!(Bool, 1),
        flags: f!(ALIAS)
    };

    EQ "meq" "eq" "==" {
        signature: s!(Bitstring, Bitstring -> Bool),
    };

    MITE "bitstring_if_then_else" "mite" "ite" {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(CUSTOM_DEDUCE)
    };

    TRUE "mtrue" "true" {
        signature: s!(() -> Bool),
    };

    FALSE "mfalse" "false" {
        signature: s!(() -> Bool),
    };

    // base bitstrings

    TUPLE "mtuple" "tuple" "pair" {
        signature: s!(Bitstring, 2)
    };

    PROJ_1 "sel1of2" "p1" "fst" {
        signature: s!(Bitstring, 1)
    };

    PROJ_2 "sel2of2" "p2" "snd" {
        signature: s!(Bitstring, 1)
    };

    EMPTY "mempty" "empty" "none" {
        signature: s!(Bitstring, 0)
    };

    // ptcl

    HAPPENS "happens" {
        signature: s!(Time -> Bool),
    };

    LT "lt" "<" {
        signature: s!(Time, Time -> Bool),
    };

    LEQ "leq" "<=" {
        signature: s!(Time, Time -> Bool),
    };

    PRED "pred" {
        signature: s!(Time, 1),
    };

    // macro

    ATT "att" {
        signature: s!(Time -> Bitstring),
    };

    MACRO_INPUT "macro_input" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(MACRO)
    };

    MACRO_FRAME "macro_frame" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(MACRO)
    };

    MACRO_MSG "macro_msg" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(MACRO)
    };

    MACRO_COND "macro_cond" {
        signature: s!(Time, Protocol -> Bool),
        flags: f!(MACRO)
    };

    MACRO_EXEC "macro_exec" {
        signature: s!(Time, Protocol -> Bool),
        flags: f!(MACRO)
    };

    UNFOLD_INPUT "unfold_input" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(UNFOLD)
    };

    UNFOLD_FRAME "unfold_frame" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(UNFOLD)
    };

    UNFOLD_MSG "unfold_msg" {
        signature: s!(Time, Protocol -> Bitstring),
        flags: f!(UNFOLD)
    };

    UNFOLD_COND "unfold_cond" {
        signature: s!(Time, Protocol -> Bool),
        flags: f!(UNFOLD)
    };

    UNFOLD_EXEC "unfold_exec" {
        signature: s!(Time, Protocol -> Bool),
        flags: f!(UNFOLD)
    };


    // prolog only

    GOAL "goal" {
        signature: s!(() -> Bool), // kinda irrelevant here
        flags: f!(PROLOG_ONLY)
    };

    BOOL_DEDUCE "deduce_bool" "deduce_b" {
        signature: s!(
                /* hypothesis */
                Bitstring, Bitstring, 
                /* to prove */
                Bool, Bool,
                /* constrains */
                Bool, Bool
            -> Bool),
        flags: f!(PROLOG_ONLY)
    };
    
    BIT_DEDUCE "deduce_bitstring" "deduce_m" {
        signature: s!(
            /* hypothesis */
            Bitstring, Bitstring, 
            /* to prove */
            Bitstring, Bitstring,
            /* constrains */
            Bool, Bool
            -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    EQUIV "equiv" {
        signature: s!(
            /* hypothesis */
            Bitstring, Bitstring, 
            /* to prove */
            Bitstring, Bitstring 
            -> Bool),
        flags: f!(PROLOG_ONLY)
    };
);
