mod step;
use std::fmt::Display;

use egg::RecExpr;
pub use step::Step;

#[allow(clippy::module_inception)]
mod protocol;
pub use protocol::Protocol;

use crate::terms::{
    Function, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, UNFOLD_COND,
    UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG,
};

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MacroKind {
    Frame,
    Input,
    Cond,
    Msg,
    Exec,
}

impl MacroKind {
    pub const fn get_unfold(self) -> &'static Function {
        match self {
            MacroKind::Frame => &UNFOLD_FRAME,
            MacroKind::Input => &UNFOLD_INPUT,
            MacroKind::Cond => &UNFOLD_COND,
            MacroKind::Msg => &UNFOLD_MSG,
            MacroKind::Exec => &UNFOLD_EXEC,
        }
    }

    pub const fn get_macro(self) -> &'static Function {
        match self {
            MacroKind::Frame => &MACRO_FRAME,
            MacroKind::Input => &MACRO_INPUT,
            MacroKind::Cond => &MACRO_COND,
            MacroKind::Msg => &MACRO_MSG,
            MacroKind::Exec => &MACRO_EXEC,
        }
    }
}

impl Display for MacroKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl MacroKind {
    pub const fn all() -> [Self; 5] {
        use MacroKind::*;
        [Frame, Input, Cond, Msg, Exec]
    }
}

/// This is a shortcut for [join_recexprs]. It expects the childrens of `fun` to
/// be `0..args.length()`.
///
/// [join_recexprs]: egg::Language::join_recexprs
#[inline]
fn apply_rec_exprs<L, Expr>(fun: &L, args: &[Expr]) -> RecExpr<L>
where
    L: egg::Language + Display,
    Expr: AsRef<[L]>,
{
    fun.join_recexprs(|i| &args[usize::from(i)])
}

// #[cfg(test)]
// pub mod test;
