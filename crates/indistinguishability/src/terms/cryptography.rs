//! Dumb module to define some of the data regarding cryptopgrahy

use utils::dynamic_iter;

use crate::{
    MSmt, Problem,
    rules::{self, mk_no_guessing_smt},
};

#[derive(Debug, Default)]
#[non_exhaustive]
pub enum CryptographicAssumption {
    #[default]
    Undefined,
    PRF(rules::PRF),
    NoGuessingTh,
}

impl CryptographicAssumption {
    /// update the prelude when needed
    pub fn mk_prelude<'a>(&'a self, pbl: &'a Problem) -> impl Iterator<Item = MSmt> + use<'a> {
        dynamic_iter!(Ret; NGTH:A, Empty:B);

        match self {
            Self::NoGuessingTh => Ret::NGTH(mk_no_guessing_smt(pbl)),
            _ => Ret::Empty(::std::iter::empty()),
        }
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
