use utils::string_ref::StrRef;

use crate::environement::traits::{KnowsRealm, Realm};
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::{BITSTRING, BOOL};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum TermBase {
    Bool,
    Condition,
    Message,
    Bitstring,
}

pub mod constants {
    pub const MESSAGE_NAME: &str = "Message";
    pub const BOOL_NAME: &str = "Bool";
    pub const CONDITION_NAME: &str = "Condition";
    pub const BITSTRING_NAME: &str = "Bitstring";
}

impl TermBase {
    pub fn evaluated_sort<'a>(&self) -> Option<Sort<'a>> {
        match self {
            Self::Condition => Some(BOOL.as_sort()),
            Self::Message => Some(BITSTRING.as_sort()),
            _ => None,
        }
    }

    pub fn is_evaluated(&self) -> bool {
        self.evaluated_sort().is_none()
    }

    pub fn name(&self) -> StrRef<'static> {
        match self {
            TermBase::Bool => constants::BOOL_NAME,
            TermBase::Condition => constants::CONDITION_NAME,
            TermBase::Message => constants::MESSAGE_NAME,
            TermBase::Bitstring => constants::BITSTRING_NAME,
        }
        .into()
    }

    /// Returns `true` if the base is [`Bool`].
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Returns `true` if the base is [`Condition`].
    #[must_use]
    pub fn is_condition(&self) -> bool {
        matches!(self, Self::Condition)
    }

    /// Returns `true` if the base is [`Message`].
    #[must_use]
    pub fn is_message(&self) -> bool {
        matches!(self, Self::Message)
    }

    /// Returns `true` if the base is [`Bitstring`].
    #[must_use]
    pub fn is_bitstring(&self) -> bool {
        matches!(self, Self::Bitstring)
    }

    pub fn list() -> [Self; 4] {
        [Self::Bool, Self::Condition, Self::Message, Self::Bitstring]
    }
}

impl KnowsRealm for TermBase {
    fn get_realm(&self) -> Realm {
        if self.is_evaluated() {
            Realm::Evaluated
        } else {
            Realm::Symbolic
        }
    }
}
