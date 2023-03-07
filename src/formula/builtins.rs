pub mod types {
    use crate::formula::env::Environement;

    use super::super::sort::Sort;
    use super::macros::new_type;
    use paste::paste;

    new_type!(BOOL, "Bool");
    new_type!(MSG, "Message");
    new_type!(NONCE, "Nonce");
    new_type!(STEP, "Step");
    new_type!(BITSTRING, "t$Bitstring");
    new_type!(CONDITION, "t$Condition");
}

pub mod functions {
    use crate::formula::env::Environement;
    use crate::formula::formula::RichFormula;

    use crate::formula::macros::fun;

    use super::super::function::Function;
    use super::macros::new_fun;
    use paste::paste;

    new_fun!(NONCE_MSG, "m$nonce_as_msg");
    new_fun!(IF_THEN_ELSE, "m$ite");
    new_fun!(B_IF_THEN_ELSE, "ite");
    new_fun!(BOOL_IF_THEN_ELSE, "ite");
    new_fun!(AND, "and");
    new_fun!(OR, "or");
    new_fun!(NOT, "not");
    new_fun!(TRUE, "true");
    new_fun!(FALSE, "false");
    new_fun!(EQUALITY, "=");
    new_fun!(B_EQUALITY, "=");
    new_fun!(INPUT, "input");
    new_fun!(FAIL, "fail");
    new_fun!(EMPTY, "empty");
    new_fun!(LT, "lt");
    new_fun!(HAPPENS, "happens");
    new_fun!(IMPLIES, "=>");

    // new_fun!(EVAL_MSG, "m$eval");
    // new_fun!(EVAL_COND, "c$eval");
    pub const EVAL_COND_NAME: &'static str = "c$eval";
    pub const EVAL_MSG_NAME: &'static str = "m$eval";

    new_fun!(SUBTERM, "subterm");

    pub fn f_true(env: &Environement) -> RichFormula {
        fun!(TRUE(env); )
    }

    pub fn f_false(env: &Environement) -> RichFormula {
        fun!(FALSE(env); )
    }

    pub fn f_and(env: &Environement, a: RichFormula, b: RichFormula) -> RichFormula {
        fun!(AND(env); a, b)
    }

    pub fn f_or(env: &Environement, a: RichFormula, b: RichFormula) -> RichFormula {
        fun!(OR(env); a, b)
    }

    pub fn not(env: &Environement, a: RichFormula) -> RichFormula {
        fun!(NOT(env); a)
    }

    pub fn implies(env: &Environement, a: RichFormula, b: RichFormula) -> RichFormula {
        fun!(IMPLIES(env); a, b)
    }
}

pub mod steps {
    use crate::{
        formula::{env::Environement, formula::RichFormula},
        problem::step::Step,
    };

    use super::functions::{EMPTY, TRUE};

    #[allow(non_snake_case)]
    pub fn INIT(env: &Environement) -> Step {
        let f = env.get_f(INIT_NAME).unwrap().clone();
        Step::new(
            INIT_NAME,
            vec![],
            RichFormula::Fun(TRUE(env).clone(), vec![]),
            RichFormula::Fun(EMPTY(env).clone(), vec![]),
            f,
        )
    }
    pub const INIT_NAME: &str = "s$init";
}

pub mod init {
    use std::collections::HashMap;

    use crate::formula::env::Environement;
    use crate::formula::function::FFlags;
    use crate::formula::sort::SFlags;

    use super::super::function::Function;
    use super::super::sort::Sort;
    use super::{
        functions::*,
        macros::{init_fun, init_sort},
        steps::*,
        types::*,
    };

    use paste::paste;
    pub fn init_env(
        env: &mut Environement,
        h: impl Fn(&mut Environement) -> &mut HashMap<String, Sort>,
    ) {
        let extra_evaluatable = if env.no_ta() {
            SFlags::EVALUATABLE
        } else {
            Default::default()
        };

        init_sort!(env; BOOL; SFlags::BUILTIN_VAMPIRE | extra_evaluatable);
        init_sort!(env; NONCE);
        init_sort!(env; STEP; SFlags::TERM_ALGEBRA);
        init_sort!(env; BITSTRING; extra_evaluatable);
        if env.no_ta() {
            let bitstring = BITSTRING(env).clone();
            let bool = BOOL(env).clone();

            let h = h(env);

            h.insert(MSG_NAME.to_owned(), bitstring);
            h.insert(CONDITION_NAME.to_owned(), bool);
        } else {
            init_sort!(env; MSG; SFlags::TERM_ALGEBRA | SFlags::EVALUATABLE);
            init_sort!(env; CONDITION; SFlags::TERM_ALGEBRA | SFlags::EVALUATABLE);
        }

        init_fun!(env; NONCE_MSG; NONCE ; MSG; FFlags::TERM_ALGEBRA);
        init_fun!(env; IF_THEN_ELSE; BOOL, MSG, MSG ; MSG; FFlags::TERM_ALGEBRA | FFlags::SPECIAL_EVALUATE);
        init_fun!(env; B_IF_THEN_ELSE; BOOL, BITSTRING, BITSTRING ; BITSTRING; FFlags::EVALUATE_TA | FFlags::BUILTIN);
        init_fun!(env; BOOL_IF_THEN_ELSE; BOOL, BOOL, BOOL ; BOOL; FFlags::BUILTIN);
        init_fun!(env; AND; BOOL, BOOL ; BOOL; FFlags::BUILTIN);
        init_fun!(env; OR; BOOL, BOOL ; BOOL; FFlags::BUILTIN);
        init_fun!(env; NOT; BOOL ; BOOL; FFlags::BUILTIN);
        init_fun!(env; TRUE; ; BOOL; FFlags::BUILTIN);
        init_fun!(env; FALSE; ; BOOL; FFlags::BUILTIN);
        init_fun!(env; EQUALITY; MSG, MSG; BOOL; FFlags::BUILTIN);
        init_fun!(env; B_EQUALITY; BITSTRING, BITSTRING; BOOL; FFlags::EVALUATE_TA | FFlags::BUILTIN);
        init_fun!(env; INPUT; STEP; MSG; FFlags::TERM_ALGEBRA | FFlags::SPECIAL_EVALUATE | FFlags::SPECIAL_SUBTERM);
        init_fun!(env; FAIL; ; MSG; FFlags::TERM_ALGEBRA);
        init_fun!(env; EMPTY; ; MSG; FFlags::TERM_ALGEBRA);
        init_fun!(env; LT; STEP, STEP; BOOL);
        init_fun!(env; HAPPENS; STEP; BOOL);
        init_fun!(env; IMPLIES; BOOL, BOOL; BOOL; FFlags::BUILTIN);
        init_fun!(env; EVAL_MSG; MSG; BITSTRING);
        init_fun!(env; EVAL_COND; CONDITION; BOOL);
        init_fun!(env; SUBTERM; BOOL, BOOL, BOOL; BOOL ; FFlags::BUILTIN);

        init_fun!(env; INIT; ; STEP; Function::step_flags());
    }
}

mod macros {

    macro_rules! new_type {
        ($name:ident, $content:literal) => {
            paste! {
                pub const [<$name _NAME>]:&'static str = $content;

                #[allow(non_snake_case)]
                pub fn $name(env: &Environement) -> &Sort {
                    env.get_s([<$name _NAME>]).unwrap()
                }
            }
        };
    }

    macro_rules! new_fun {
        ($name:ident, $name2:literal) => {
            paste! {
                pub const [<$name _NAME>]:&'static str = $name2;

                #[allow(non_snake_case)]
                pub fn $name(env: &Environement) -> &Function {
                    env.get_f([<$name _NAME>]).unwrap()
                }
            }
        };
    }

    macro_rules! init_fun {
        ($env:expr; $name:ident; $($in_s:ident),*; $out_s:ident; $flags:expr) => {
            {paste! {
                let f = Function::new_with_flag([<$name _NAME>], vec![$($in_s($env).clone()),*], $out_s($env).clone(), $flags);
                $env.add_f(f.clone());
                f
            }}
        };
        ($env:expr; $name:ident; $($in_s:ident),*; $out_s:ident) => {
            paste! {
                // env.add_f(Function::new_with_flag([<$name _NAME>], vec![$($in_s(env).clone()),*], $out_s(env).clone(), FFlags::empty))
                init_fun!($env; $name; $($in_s),*; $out_s; FFlags::empty())
            }
        };
    }

    macro_rules! init_sort {
        ($env:expr; $name:ident; $flags:expr) => {
            paste! {
                $env.add_s(Sort::new_with_flag([<$name _NAME>], $flags))
            }
        };
        ($env:expr; $name:ident) => {
            paste! {
                init_sort!($env; $name; SFlags::empty())
            }
        };
    }

    pub(crate) use {init_fun, init_sort, new_fun, new_type};
}
