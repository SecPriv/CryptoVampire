//! Dumb module to define some of the data regarding cryptopgrahy

use utils::dynamic_iter;

use crate::libraries::{self, mk_no_guessing_smt};
use crate::{MSmt, Problem};

/// Represents different cryptographic assumptions that can be made in the problem.
#[derive(Debug, Default)]
#[non_exhaustive]
pub enum CryptographicAssumption {
    #[default]
    Undefined,
    PRF(libraries::PRF),
    AEnc(libraries::AEnc),
    XOr(libraries::XOr),
    DDH(libraries::DDH),
    NoGuessingTh,
}

impl CryptographicAssumption {
    /// Generates SMT prelude statements based on the cryptographic assumption.
    pub fn mk_prelude<'a>(&'a self, pbl: &'a Problem) -> impl Iterator<Item = MSmt> + use<'a> {
        dynamic_iter!(Ret; NGTH:A, Empty:B);

        match self {
            Self::NoGuessingTh => Ret::NGTH(mk_no_guessing_smt(pbl)),
            _ => Ret::Empty(::std::iter::empty()),
        }
    }

    #[must_use]
    pub fn as_prf(&self) -> Option<&libraries::PRF> {
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

    /// Returns `true` if the cryptographic assumption is [`AEnc`].
    ///
    /// [`AEnc`]: CryptographicAssumption::AEnc
    #[must_use]
    pub fn is_aenc(&self) -> bool {
        matches!(self, Self::AEnc(..))
    }

    #[must_use]
    pub fn as_aenc(&self) -> Option<&libraries::AEnc> {
        if let Self::AEnc(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the cryptographic assumption is [`XOr`].
    ///
    /// [`XOr`]: CryptographicAssumption::XOr
    #[must_use]
    pub fn is_xor(&self) -> bool {
        matches!(self, Self::XOr(..))
    }

    #[must_use]
    pub fn as_xor(&self) -> Option<&libraries::XOr> {
        if let Self::XOr(v) = self {
            Some(v)
        } else {
            None
        }
    }

    /// Returns `true` if the cryptographic assumption is [`DDH`].
    ///
    /// [`DDH`]: CryptographicAssumption::DDH
    #[must_use]
    pub fn is_ddh(&self) -> bool {
        matches!(self, Self::DDH(..))
    }

    #[must_use]
    pub fn as_ddh(&self) -> Option<&libraries::DDH> {
        if let Self::DDH(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl From<libraries::PRF> for CryptographicAssumption {
    /// Converts a `rules::PRF` into a `CryptographicAssumption::PRF`.
    fn from(v: libraries::PRF) -> Self {
        Self::PRF(v)
    }
}

impl From<libraries::AEnc> for CryptographicAssumption {
    fn from(v: libraries::AEnc) -> Self {
        Self::AEnc(v)
    }
}

impl From<libraries::XOr> for CryptographicAssumption {
    fn from(v: libraries::XOr) -> Self {
        Self::XOr(v)
    }
}

impl From<libraries::DDH> for CryptographicAssumption {
    fn from(v: libraries::DDH) -> Self {
        Self::DDH(v)
    }
}
