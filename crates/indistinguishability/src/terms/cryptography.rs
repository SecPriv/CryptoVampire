//! Dumb module to define some of the data regarding cryptopgrahy

use crate::{problem::RcRule, rules, terms::Function, MSmt, Problem};


#[derive(Debug, Default)]
#[non_exhaustive]
pub enum CryptographicAssumption {
    #[default]
    Undefined,
    PRF(rules::PRF),
}

impl CryptographicAssumption {

    pub fn mk_prelude(&self, pbl: &Problem) -> impl Iterator<Item = MSmt> + use<'_> {
        [].into_iter()
    }

    #[must_use]
    pub fn as_prf(&self) -> Option<&rules::PRF> {
        if let Self::PRF(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the cryptographic assumption is [`Undefined`].
    ///
    /// [`Undefined`]: CryptographicAssumption::Undefined
    #[must_use]
    pub fn is_undefined(&self) -> bool {
        matches!(self, Self::Undefined)
    }

    /// Returns `true` if the cryptographic assumption is [`PRF`].
    ///
    /// [`PRF`]: CryptographicAssumption::PRF
    #[must_use]
    pub fn is_prf(&self) -> bool {
        matches!(self, Self::PRF(..))
    }
}

impl From<rules::PRF> for CryptographicAssumption {
    fn from(v: rules::PRF) -> Self {
        Self::PRF(v)
    }
}