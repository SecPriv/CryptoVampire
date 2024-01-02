use crate::{
    environement::traits::{KnowsRealm, Realm},
    formula::sort::{
        builtins::{BITSTRING, BOOL},
        Sort,
    },
};
use utils::string_ref::StrRef;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum TermBase {
    Bool,
    Condition,
    Message,
    Bitstring,
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
            TermBase::Bool => "Bool",
            TermBase::Condition => "Condition",
            TermBase::Message => "Message",
            TermBase::Bitstring => "Bitstring",
        }
        .into()
    }

    /// Returns `true` if the base is [`Bool`].
    ///
    /// [`Bool`]: Base::Bool
    #[must_use]
    pub fn is_bool(&self) -> bool {
        matches!(self, Self::Bool)
    }

    /// Returns `true` if the base is [`Condition`].
    ///
    /// [`Condition`]: Base::Condition
    #[must_use]
    pub fn is_condition(&self) -> bool {
        matches!(self, Self::Condition)
    }

    /// Returns `true` if the base is [`Message`].
    ///
    /// [`Message`]: Base::Message
    #[must_use]
    pub fn is_message(&self) -> bool {
        matches!(self, Self::Message)
    }

    /// Returns `true` if the base is [`Bitstring`].
    ///
    /// [`Bitstring`]: Base::Bitstring
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
