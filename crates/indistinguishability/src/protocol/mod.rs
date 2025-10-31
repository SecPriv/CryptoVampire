/// Defines the structure and behavior of a single step within a cryptographic protocol.
mod step;
use std::fmt::Display;

/// Re-exports the `Step` struct, representing a single step in a cryptographic protocol.
pub use step::Step;

/// Defines the structure and behavior of a cryptographic protocol.
#[allow(clippy::module_inception)]
mod protocol;
/// Re-exports the `Protocol` struct, representing a cryptographic protocol.
pub use protocol::Protocol;

use crate::terms::{
    Function, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, UNFOLD_COND,
    UNFOLD_EXEC, UNFOLD_FRAME, UNFOLD_INPUT, UNFOLD_MSG,
};

/// Represents the different kinds of macros used in the protocol analysis.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum MacroKind {
    /// Represents the frame macro.
    Frame,
    /// Represents the input macro.
    Input,
    /// Represents the condition macro.
    Cond,
    /// Represents the message macro.
    Msg,
    /// Represents the execution macro.
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
    /// Formats the `MacroKind` for display.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl MacroKind {
    /// Returns an array containing all variants of `MacroKind`.
    pub const fn all() -> [Self; 5] {
        use MacroKind::*;
        [Frame, Input, Cond, Msg, Exec]
    }
}
