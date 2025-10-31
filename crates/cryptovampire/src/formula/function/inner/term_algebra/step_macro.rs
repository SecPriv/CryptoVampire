use utils::match_as_trait;

use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{FixedSignature, MaybeEvaluatable};
use crate::formula::sort::builtins::{CONDITION, MESSAGE, STEP};
use crate::formula::utils::formula_expander::UnfoldFlags;
use crate::problem::cell_dependancies::MacroRef;
use crate::static_signature;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum Macro {
    Condition,
    Message,
    Exec,
    Input,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum MessageOrCondition {
    Message,
    Condition,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum InputOrExec {
    Input,
    Exec,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum MacroKind {
    Step(MessageOrCondition),
    Rec(InputOrExec),
}

impl<'bump> MaybeEvaluatable<'bump> for Macro {
    fn maybe_get_evaluated(&self) -> Option<crate::formula::function::Function<'bump>> {
        None
    }
}

// for now
static_signature!(STEP_MESSAGE_SIGNATURE: (STEP) -> MESSAGE);
static_signature!(STEP_CONDITION_SIGNATURE: (STEP) -> CONDITION);
static_signature!(STEP_EXEC_SIGNATURE: (STEP) -> CONDITION);
static_signature!(STEP_INPUT_SIGNATURE: (STEP) -> MESSAGE);

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Macro {
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        match self {
            Self::Condition => STEP_CONDITION_SIGNATURE.as_ref(),
            Self::Message => STEP_MESSAGE_SIGNATURE.as_ref(),
            Self::Exec => STEP_EXEC_SIGNATURE.as_ref(),
            Self::Input => STEP_INPUT_SIGNATURE.as_ref(),
        }
    }
}

impl Macro {
    pub const fn name(&self) -> &'static str {
        match self {
            Self::Condition => "cond",
            Self::Message => "msg",
            Self::Exec => "exec",
            Self::Input => "input",
        }
    }

    pub const fn unfold_flag(&self) -> UnfoldFlags {
        self.into_kind().unfold_flag()
    }

    pub const fn into_kind(&self) -> MacroKind {
        match self {
            Macro::Condition => MacroKind::Step(MessageOrCondition::Condition),
            Macro::Message => MacroKind::Step(MessageOrCondition::Message),
            Macro::Exec => MacroKind::Rec(InputOrExec::Exec),
            Macro::Input => MacroKind::Rec(InputOrExec::Input),
        }
    }
}

impl From<Macro> for MacroKind {
    fn from(value: Macro) -> Self {
        value.into_kind()
    }
}

impl From<MessageOrCondition> for Macro {
    fn from(value: MessageOrCondition) -> Self {
        match value {
            MessageOrCondition::Message => Macro::Message,
            MessageOrCondition::Condition => Macro::Condition,
        }
    }
}

impl From<InputOrExec> for Macro {
    fn from(value: InputOrExec) -> Self {
        match value {
            InputOrExec::Input => Macro::Input,
            InputOrExec::Exec => Macro::Exec,
        }
    }
}

impl From<MacroKind> for Macro {
    fn from(value: MacroKind) -> Self {
        match_as_trait!(value => {MacroKind::Rec(x) | MacroKind::Step(x) => {x.into()}})
    }
}

impl MacroKind {
    pub const fn unfold_flag(&self) -> UnfoldFlags {
        match_as_trait!(self => {MacroKind::Rec(x) | MacroKind::Step(x) => {x.unfold_flag()}})
    }
}

impl MessageOrCondition {
    pub const fn unfold_flag(&self) -> UnfoldFlags {
        UnfoldFlags::UNFOLD_STEP_MACROS
    }
}

impl InputOrExec {
    pub const fn into_macro_ref<'bump>(&self) -> MacroRef<'bump> {
        match self {
            InputOrExec::Input => MacroRef::Input,
            InputOrExec::Exec => MacroRef::Exec,
        }
    }
    pub const fn unfold_flag(&self) -> UnfoldFlags {
        match self {
            Self::Exec => UnfoldFlags::UNFOLD_EXEC,
            Self::Input => UnfoldFlags::UNFOLD_INPUT,
        }
    }

    pub const fn all_unfold_flags(&self) -> UnfoldFlags {
        UnfoldFlags::union(UnfoldFlags::UNFOLD_EXEC, UnfoldFlags::UNFOLD_INPUT)
    }
}
