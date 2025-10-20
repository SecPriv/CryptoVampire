use std::borrow::Cow;

use cryptovampire_macros::mk_builtin_funs;

use super::Sort::{self, *};
use super::{Alias, AliasRewrite, Function, FunctionFlags, InnerFunction, Signature};
use crate::rexp;

/// helper to write const signatures
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

macro_rules! mk_static_slice {
    ($ty:ty; [$($e:expr),*]) => {
        {
            static TMP : &'static [$ty] = &[$($e),*];
            TMP
        }
    };
}

macro_rules! alias {
    ($( $($var:ident:$sort:ident),* in $($args:expr),* => $to:expr),*) => {
        {
            Alias(Cow::Borrowed(mk_static_slice!(AliasRewrite;
            [$({
                $(
                    #[allow(non_upper_case_globals)]
                    static $var: $crate::terms::Variable = $crate::fresh!(const $sort);
                )*
                {
                    let variables = Cow::Borrowed(mk_static_slice!($crate::terms::Variable; [$($var.const_clone()),*]));


                    AliasRewrite {
                        from: Cow::Borrowed(mk_static_slice!($crate::terms::RecFOFormula; [$($args),*])),
                        to: $to,
                        variables,
                    }
                }
            }),*]
            )))
        }
    };
}

// -----------------------------------------------------------------------------
// ---------------------------------- sorts ------------------------------------
// -----------------------------------------------------------------------------

pub static SORT_LIST: [Sort; 6] = {
    use Sort::*;
    [Bool, Bitstring, Time, Protocol, Nonce, Index]
};

/// [Sort]s to be declared in smt
pub static SMT_SORT_LIST: [Sort; 3] = {
    use Sort::*;
    [Bitstring, Time, /* Protocol, Nonce, */ Index]
};

// -----------------------------------------------------------------------------
// -------------------------------- functions ----------------------------------
// -----------------------------------------------------------------------------

mk_builtin_funs!(
    // The "default" value.
    //
    // The field declared here will be copied in every struct, unless it is overwitten
    {
        flags: FunctionFlags::BUILTIN,
        quantifier_idx: 0,
        protocol_idx: 0,
        alias: None,
        step_idx: 0,
        cryptography: Cow::Borrowed(&[])
    };

    // =========================================================
    // ===================== the structs =======================
    // =========================================================

    // ~~~~~~~~~~~~~~~~~ bool ~~~~~~~~~~~~~~~~~~~

    /// boolean `if-then-else` in the sens that it returns a [Sort::Bool]
    BITE "b_ite" "bool_if_then_else" {
        signature: s!(Bool, 3),
        flags: f!(CUSTOM_DEDUCE | BUILTIN_SMT | IF_THEN_ELSE)
    };

    /// bitstring `if-then-else` in the sens that it returns a [Sort::Bitstring]
    MITE "m_ite" "bitstring_if_then_else" {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(CUSTOM_DEDUCE | BUILTIN_SMT | IF_THEN_ELSE)
    };

    /// Regular `implies`, i.e., `a => b`.
    /// This function is used in the [rexp] macro for `=>`
    ///
    /// *NB*: this is an alias for [BITE]
    IMPLIES "mimplies" "bit_implies" "implies" "=>" {
        signature: s!(Bool, 2),
        flags: f!(BUILTIN_SMT), // e.g., this will be `BUILTIN | BUILTIN_SMT` instead of `FunctionFlags::BUILTIN`
        alias: Some(alias!{ // <- magic
            a:Bool, b:Bool in rexp!(const !a), rexp!(const !b) => rexp!(const (BITE !a !b true))
        }),
    };

    /// Regular `and`, i.e., `a /\ b`.
    /// This function is used in the [rexp] macro for `and``
    ///
    /// *NB*: this is an alias for [BITE]
    AND "mand" "bit_and" "and"  {
        signature: s!(Bool, 2),
        flags: f!(/* ALIAS | */ BUILTIN_SMT | CUSTOM_DEDUCE),
        // alias: Some(alias!{
        //     a:Bool, b:Bool in rexp!(const !a), rexp!(const !b) => rexp!(const (BITE !a !b false))
        // }),
    };

    /// Regular `or`
    /// This function is used in the [rexp] macro for `or``
    ///
    /// *NB*: this is an alias for [BITE]
    OR "mor" "bit_or" "or" {
        signature: s!(Bool, 2),
        flags: f!(/* ALIAS | */ BUILTIN_SMT),
        alias: Some(alias!{
            a:Bool, b:Bool in rexp!(const !a), rexp!(const !b) => rexp!(const (BITE !a true !b))
        }),
    };

    /// Regular not
    /// This function is used in the [rexp] macro for `not``
    ///
    /// *NB*: this is an alias for [BITE]
    NOT "mnot" "bit_not" "not" {
        signature: s!(Bool, 1),
        flags: f!(/* ALIAS | */ BUILTIN_SMT),
        // alias: Some(alias!{
        //     a:Bool in rexp!(const !a) => rexp!(const (BITE !a false true))
        // }),
    };

    /// Bitstring equality. This what is used as `=` in [rexp]
    EQ "eq" "==" "meq" {
        signature: s!(Bitstring, Bitstring -> Bool),
        flags: f!(BUILTIN_SMT)
    };

    TRUE "mtrue" "true" {
        signature: s!(() -> Bool),
        flags: f!(BUILTIN_SMT)
    };

    FALSE "mfalse" "false" {
        signature: s!(() -> Bool),
        flags: f!(BUILTIN_SMT)
    };

    // ~~~~~~~~~~~ base bitstrings ~~~~~~~~~~~~~~

    NONCE "mnonce" "nonce" {
        signature: s!(Nonce -> Bitstring),
        flags: f!(CUSTOM_DEDUCE /* | CUSTOM_SUBTERM */)
    };

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

    /// Converst [Sort::Bool] to [Sort::Bitstring]
    FROM_BOOL "mfrom_bool" {
        signature: s!(Bool -> Bitstring)
    };

    // ~~~~~~~~~~~~~~~~~ ptcl ~~~~~~~~~~~~~~~~~~~

    HAPPENS "happens" {
        signature: s!(Time -> Bool),
    };

    /// *NB*: [LT] and [LEQ] are different functions. Neither is defined as the
    /// alias of the other
    LT "lt" "<" {
        signature: s!(Time, Time -> Bool),
    };

    /// *NB*: [LT] and [LEQ] are different functions. Neither is defined as the
    /// alias of the other
    LEQ "leq" "<=" {
        signature: s!(Time, Time -> Bool),
    };

    PRED "pred" {
        signature: s!(Time, 1),
    };

    /// The `init` step. It's always part of a protocol (added by default in
    /// position `0`)
    INIT "init" {
        signature: s!(Time, 0),
        flags: f!(STEP),
        step_idx: 0,
    };

    // ~~~~~~~~~~~~~~~~ macro ~~~~~~~~~~~~~~~~~~~

    ATT "att" {
        signature: s!(Bitstring -> Bitstring),
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


    // ~~~~~~~~~~~~~ prolog only ~~~~~~~~~~~~~~~~

    GOAL "goal" {
        signature: s!(Bool -> Bool), // kinda irrelevant here
        flags: f!(PROLOG_ONLY)
    };

    /// Shortcuts to failling
    FAIL "fail" {
        signature: s!(() -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    /// `u,v |> a,b | h, h'` in that order, where `a` and `b` are [Bool]s
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

    /// `u,v |> a,b | h, h'` in that order, where `a` and `b` are [Bitstring]s
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

    /// `u ~ v |- a ~ b` in that order
    EQUIV "equiv" {
        signature: s!(
            /* hypothesis */
            Bitstring, Bitstring,
            /* to prove */
            Bitstring, Bitstring
            -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    /// `FRESH_NONCE(n, u, h)` checks (with `vampire`) that the [Nonce] `n`
    /// doesn't appear in `u` when `h` holds
    FRESH_NONCE "mfresh_nonce" "fresh_nonce" {
                /* nonce -> look into -> constrains -> Bool */
        signature: s!(Nonce, Bitstring, Bool -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    /// The goal needs to be offloaded to `vampire`
    VAMPIRE "mvampire" "vampire" "smt" {
        signature: s!(Bool -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    SUBSTITUTION "msubst" {
        signature: s!(Any, Bitstring, Bitstring -> Any),
        flags: f!(PROLOG_ONLY)
    };

    SUBSTITUTION_RULE "msubst_rule" {
        signature: s!(Bool -> Bool),
        flags: f!(PROLOG_ONLY)
    };

    // -------- lambda -----------

    // LAMBDA_LET "λlet" {
    //     flags: f!(PROLOG_ONLY),
    //     signature: s!(Any, Any -> Any)
    // };

    LAMBDA_S "λS" {
        flags: f!(PROLOG_ONLY),
        signature: s!(Any -> Any)
    };

    LAMBDA_O "λO" {
        flags: f!(PROLOG_ONLY),
        signature: s!(() -> Any)
    };

    LAMBDA_LET "λlet" {
        flags: f!(PROLOG_ONLY),
        /* var count, message, content */
        signature: s!(Any, Any, Any -> Any)
    };

    ADD_S "add_λS" {
        flags: f!(PROLOG_ONLY),
        signature: s!(Any /*a list */, Any -> Any)
    };

    // ------ quantifiers --------

    /// The binder for `exists`
    ///
    /// The first argument is a list of sorts
    EXISTS "lambda_exists" {
        signature: s!(Any /* list */, Bool -> Bool),
        flags: f!(BINDER | PROLOG_ONLY)
    };

    /// The binder for `find such that`
    ///
    /// The first argument is a list of sorts. Then its `condition`,
    /// `then_branch` and `else_branch`
    FIND_SUCH_THAT "lambda_find_such_that" {
        signature: s!(Any /* list */,
            Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(BINDER | PROLOG_ONLY)
    };

    // --------- sorts -----------

    BITSTRING_SORT "bitstring_sort" {
        signature: s!(() -> Any),
        flags: f!(PROLOG_ONLY | SORT)
    };

    INDEX_SORT "index_sort" {
        signature: s!(() -> Any),
        flags: f!(PROLOG_ONLY | SORT)
    };

    TIME_SORT "time_sort" "step_sort" {
        signature: s!(() -> Any),
        flags: f!(PROLOG_ONLY | SORT)
    };

    // --------- list ------------

    CONS "list_cons" {
        signature: s!(Any, Any -> Any),
        flags : f!(PROLOG_ONLY | LIST_CONSTR)
    };

    NIL "list_nil" {
        signature: s!(() -> Any),
        flags : f!(PROLOG_ONLY | LIST_CONSTR)
    };

    // ~~~~~~~~~~~~~~~ smt only ~~~~~~~~~~~~~~~~~

    SMT_ITE "ite" {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(SMT_ONLY | BUILTIN_SMT | CUSTOM_DEDUCE | IF_THEN_ELSE)
    };

    IS_INDEPENDANT_BITSTRING "m_is_independant_bitstring" {
        signature: s!(Nonce, Bitstring -> Bool),
        flags: f!(SMT_ONLY)
    };

    IS_INDEPENDANT_BOOL "m_is_independant_bool" {
        signature: s!(Nonce, Bool -> Bool),
        flags: f!(SMT_ONLY)
    };


);
