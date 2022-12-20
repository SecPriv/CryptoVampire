pub mod types {
    use super::super::sort::Sort;
    use super::macros::new_type;
    use paste::paste;
    use static_init::dynamic;

    new_type!(BOOL, "bool");
    new_type!(MSG, "msg");
    new_type!(NONCE, "nonce");
    new_type!(STEP, "step");
    new_type!(BITSTRING, "bitstring");
    new_type!(CONDITION, "cond");
}

pub mod functions {
    use crate::formula::formula::RichFormula;
    use crate::formula::function::Flags;
    use crate::formula::macros::fun;

    use super::super::function::Function;
    use super::{macros::new_fun, types::*};
    use paste::paste;
    use static_init::dynamic;

    new_fun!(NONCE_MSG, "m$nonce_as_msg"; NONCE ; MSG; Flags::TERM_ALGEBRA);
    new_fun!(IF_THEN_ELSE, "m$ite"; BOOL, MSG, MSG ; MSG; Flags::TERM_ALGEBRA | Flags::SPECIAL_EVALUATE);
    new_fun!(B_IF_THEN_ELSE, "ite"; BOOL, BITSTRING, BITSTRING ; BITSTRING; Flags::EVALUATE_TA);
    new_fun!(AND, "and"; BOOL, BOOL ; BOOL);
    new_fun!(OR, "or"; BOOL, BOOL ; BOOL);
    new_fun!(NOT, "not"; BOOL ; BOOL);
    new_fun!(TRUE, "true"; ; BOOL);
    new_fun!(FALSE, "false"; ; BOOL);
    new_fun!(EQUALITY, "==="; MSG, MSG; BOOL);
    new_fun!(B_EQUALITY, "=="; BITSTRING, BITSTRING; BOOL; Flags::EVALUATE_TA);
    new_fun!(INPUT, "input"; STEP; MSG; Flags::TERM_ALGEBRA | Flags::SPECIAL_EVALUATE);
    new_fun!(FAIL, "fail" ; ; MSG; Flags::TERM_ALGEBRA);
    new_fun!(LT, "lt"; STEP, STEP; BOOL);
    new_fun!(HAPPENS, "happens"; STEP; BOOL);
    new_fun!(IMPLIES, "=>"; BOOL, BOOL; BOOL);

    new_fun!(EVAL_MSG, "m$eval"; MSG; BITSTRING);
    new_fun!(EVAL_COND, "c$eval"; CONDITION; BOOL);

    pub fn f_true() -> RichFormula {
        fun!(TRUE; )
    }

    pub fn f_false() -> RichFormula {
        fun!(FALSE; )
    }

    pub fn f_and(a: RichFormula, b: RichFormula) -> RichFormula {
        fun!(AND; a, b)
    }

    pub fn f_or(a: RichFormula, b: RichFormula) -> RichFormula {
        fun!(OR; a, b)
    }

    pub fn not(a: RichFormula) -> RichFormula {
        fun!(NOT; a)
    }
}

mod macros {

    macro_rules! new_type {
        ($name:ident, $content:literal) => {
            paste! {
                #[dynamic]
                pub static $name: Sort = [<$name _NAME>].into();
                pub const [<$name _NAME>]:&'static str = $content;
            }
        };
    }

    macro_rules! new_fun {
        ($name:ident, $name2:literal; $($intyp:expr),* ; $out:expr) => { paste!{
            #[dynamic]
            pub static $name: Function = Function::new([<$name _NAME>], vec![$($intyp.clone(),)*], $out.clone());
            pub const [<$name _NAME>]:&'static str = $name2;
        }};
        ($name:ident, $name2:literal; $($intyp:expr),* ; $out:expr ; $flag:expr) => { paste!{
            #[dynamic]
            pub static $name: Function = Function::new_with_flag([<$name _NAME>], vec![$($intyp.clone(),)*], $out.clone(), $flag);
            pub const [<$name _NAME>]:&'static str = $name2;
        }};
    }

    pub(crate) use {new_fun, new_type};
}
