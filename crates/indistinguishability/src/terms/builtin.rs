use super::{
    Alias, AliasRewrite, CowPattern, Function, FunctionFlags, InnerFunction, Signature,
    Sort::{self, *},
};
use cryptovampire_macros::{declare_recexpr, mk_builtin_funs};
use std::borrow::Cow;

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

macro_rules! count {
    () => {
        0
    };
    ($x: expr) => { 1};
    ($x:expr, $($other:expr),*) => {
        1 + count!($($other),*)
    };
}

macro_rules! mk_static_slice {
    ($ty:ty; [$($e:expr),*]) => {
        {
            static TMP : [$ty; count!($($e),*)] = [$($e),*];
            &TMP
        }
    };
}

macro_rules! alias {
    ($( $($var:literal:$sort:ident),* in $($args:expr),* => $to:expr),*) => {
        {
            Alias(Cow::Borrowed(mk_static_slice!(AliasRewrite;
            [$(AliasRewrite {
                    from: Cow::Borrowed(mk_static_slice!(CowPattern; [$($args),*])),
                    to: $to,
                    variables: Cow::Borrowed(mk_static_slice!(egg::Var; [$(egg::Var::from_u32($var)),*])),
                    sorts: Cow::Borrowed(mk_static_slice!(crate::terms::Sort; [$(crate::terms::Sort::$sort),*])),
                }
            ),*]
            )))
        }
    };
}

macro_rules! rexp {
    ($($t:tt)*) => {
        {
            declare_recexpr!(inner_recexpr in TMP = $($t)*);
            Cow::Borrowed(&TMP)
        }
    };
}

mod inner_recexpr {
    use egg::{Id, Var};
    use logic_formula::egg::SimplLang;

    use crate::{LangVar, terms::Function};

    #[allow(dead_code)]
    pub static TRUE: Function = super::TRUE.const_clone().unwrap();
    #[allow(dead_code)]
    pub static FALSE: Function = super::TRUE.const_clone().unwrap();
    #[allow(dead_code)]
    pub static AND: Function = super::AND.const_clone().unwrap();
    #[allow(dead_code)]
    pub static OR: Function = super::OR.const_clone().unwrap();
    #[allow(dead_code)]
    pub static NOT: Function = super::NOT.const_clone().unwrap();
    #[allow(dead_code)]
    pub static EQ: Function = super::EQ.const_clone().unwrap();
    #[allow(dead_code)]
    pub static IMPLIES: Function = super::IMPLIES.const_clone().unwrap();

    pub const fn mk_var(i: u32) -> LangVar {
        egg::ENodeOrVar::Var(Var::from_u32(i))
    }

    pub const fn mk_app<const N: usize>(head: &Function, args: [u32; N]) -> LangVar {
        let head = head.const_clone().unwrap();
        match N {
            0 => mk_app_inner(head, [0; 3], 0),
            1 => mk_app_inner(head, [args[0], 0, 0], 1),
            2 => mk_app_inner(head, [args[0], args[1], 0], 2),
            3 => mk_app_inner(head, [args[0], args[1], args[2]], 3),
            _ => panic!("N too large!"),
        }
    }

    macro_rules! mkargs {
        ($($i:expr),*) => {
            [$(Id::new_const($i)),*]
        };
    }

    const fn mk_app_inner(head: Function, [arg1, arg2, arg3]: [u32; 3], len: usize) -> LangVar {
        egg::ENodeOrVar::ENode(SimplLang::new_const(head, mkargs![arg1, arg2, arg3], len))
    }

    pub type RexpLang = LangVar;
}

// -----------------------------------------------------------------------------
// ---------------------------------- sorts ------------------------------------
// -----------------------------------------------------------------------------

pub static SORT_LIST: [Sort; 6] = {
    use Sort::*;
    [Bool, Bitstring, Time, Protocol, Nonce, Index]
};

/// [Sort]s to be declared in smt
pub static SMT_SORT_LIST: [Sort; 5] = {
    use Sort::*;
    [Bitstring, Time, Protocol, Nonce, Index]
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
        exists_idx: 0,
        protocol_idx: 0,
        alias: None,
        step_idx: 0,
        cryptography: Cow::Borrowed(&[])
    };

    // =========================================================
    // ===================== the structs =======================
    // =========================================================

    // ~~~~~~~~~~~~~~~~~ bool ~~~~~~~~~~~~~~~~~~~

    BITE "bool_if_then_else" "b_ite" {
        signature: s!(Bool, 3),
        flags: f!(CUSTOM_DEDUCE | BUILTIN_SMT | IF_THEN_ELSE)
    };

    MITE "bitstring_if_then_else" "m_ite" {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(CUSTOM_DEDUCE | BUILTIN_SMT | IF_THEN_ELSE)
    };

    IMPLIES "bit_implies" "implies" "=>" "mimplies" {
        signature: s!(Bool, 2),
        flags: f!(BUILTIN_SMT), // e.g., this will be `BUILTIN | BUILTIN_SMT` instead of `FunctionFlags::BUILTIN`
        alias: Some(alias!{ // <- magic
            0:Bool, 1:Bool in rexp!(#0), rexp!(#1) => rexp!((BITE #0 #1 TRUE))
        }),
    };

    AND "bit_and" "and" "mand" {
        signature: s!(Bool, 2),
        flags: f!(/* ALIAS | */ BUILTIN_SMT),
        alias: Some(alias!{
            0:Bool, 1:Bool in rexp!(#0), rexp!(#1) => rexp!((BITE #0 #1 FALSE))
        }),
    };

    OR "bit_or" "or" "mor" {
        signature: s!(Bool, 2),
        flags: f!(/* ALIAS | */ BUILTIN_SMT),
        alias: Some(alias!{
            0:Bool, 1:Bool in rexp!(#0), rexp!(#1) => rexp!((BITE #0 TRUE #1))
        }),
    };

    NOT "bit_not" "not" "mnot" {
        signature: s!(Bool, 1),
        flags: f!(/* ALIAS | */ BUILTIN_SMT),
        alias: Some(alias!{
            0:Bool in rexp!(#0) => rexp!((BITE #0 FALSE TRUE))
        }),
    };

    EQ "meq" "eq" "==" {
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

    FROM_BOOL "mfrom_bool" {
        signature: s!(Bool -> Bitstring)
    };

    // ~~~~~~~~~~~~~~~~~ ptcl ~~~~~~~~~~~~~~~~~~~

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

    FAIL "fail" {
        signature: s!(() -> Bool),
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

    FRESH_NONCE "mfresh_nonce" "fresh_nonce" {
                /* nonce -> look into -> constrains -> Bool */
        signature: s!(Nonce, Bitstring, Bool -> Bool),
        flags: f!(CUSTOM_DEDUCE)
    };

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

    // ~~~~~~~~~~~~~~~ smt only ~~~~~~~~~~~~~~~~~

    SMT_ITE "ite" {
        signature: s!(Bool, Bitstring, Bitstring -> Bitstring),
        flags: f!(SMT_ONLY | BUILTIN_SMT | CUSTOM_DEDUCE | IF_THEN_ELSE)
    }

);
