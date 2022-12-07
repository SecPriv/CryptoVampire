pub mod types {
    use super::super::sort::Sort;
    use super::macros::new_type;
    use paste::paste;
    use static_init::dynamic;

    new_type!(BOOL, "bool");
    new_type!(MSG, "msg");
    new_type!(NONCE, "nonce");
}

pub mod functions {
    use crate::formula::formula::Formula;

    use super::super::function::Function;
    use super::{macros::new_fun, types::*};
    use paste::paste;
    use static_init::dynamic;

    new_fun!(NONCE_MSG, "m$nonce_as_msg"; NONCE ; MSG);
    new_fun!(IF_THEN_ELSE, "m$ite"; BOOL, MSG, MSG ; MSG);
    new_fun!(AND, "and"; BOOL, BOOL ; BOOL);
    new_fun!(OR, "or"; BOOL, BOOL ; BOOL);
    new_fun!(NOT, "not"; BOOL ; BOOL);
    new_fun!(TRUE, "true"; ; BOOL);
    new_fun!(FALSE, "false"; ; BOOL);

    pub fn f_true() -> Formula {
        Formula::Fun(TRUE.clone(), vec![])
    }

    pub fn f_false() -> Formula {
        Formula::Fun(FALSE.clone(), vec![])
    }

    pub fn f_and(a: Formula, b: Formula) -> Formula {
        Formula::Fun(AND.clone(), vec![a, b])
    }

    pub fn f_or(a: Formula, b: Formula) -> Formula {
        Formula::Fun(OR.clone(), vec![a, b])
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
    }

    pub(crate) use {new_fun, new_type};
}
