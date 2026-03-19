//! Dumb module to define some of the data regarding cryptopgrahy

use std::fmt::Display;

use anyhow::{Context, bail, ensure};
use cryptovampire_smt::SmtSink;
use utils::{dynamic_iter, match_as_trait};

use crate::libraries::{self, add_no_guessing_smt};
use crate::problem::ProblemState;
use crate::terms::{Formula, Sort, Variable};
use crate::{Problem, MSmtParam};

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
    /// Returns `true` if the cryptographic assumption is [`Undefined`].
    ///
    /// [`Undefined`]: CryptographicAssumption::Undefined
    #[must_use]
    pub fn is_undefined(&self) -> bool {
        matches!(self, Self::Undefined)
    }

    #[must_use]
    pub fn as_inner<T: Cryptography>(&self) -> Option<&T> {
        T::ref_from_assumption(self)
    }
}

pub trait Cryptography: Into<CryptographicAssumption> {
    fn add_prelude(&self, _pbl: &Problem, _sink: &mut impl SmtSink<MSmtParam>) {}

    fn name(&self) -> impl Display;

    #[must_use]
    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self>;

    fn register_at(self, pbl: &mut Problem, index: usize) -> anyhow::Result<&Self> {
        let ca = pbl
            .cryptography_mut(index)
            .with_context(|| format!("no cryptography at index {index:}"))?;
        ensure!(
            ca.is_undefined(),
            "cryptography at index {index:} is already defined as:\n{ca:#?}"
        );
        *ca = self.into();
        Ok(ca.as_inner().unwrap())
    }

    fn register_nonce(
        &self,
        _pbl: &mut ProblemState,
        _variables: Vec<Variable>,
        n: Formula,
    ) -> anyhow::Result<()> {
        assert!(n.has_sort(Sort::Nonce), "nonce should have sort 'Nonce'");
        bail!("unsupported for {}", self.name())
    }
}

impl Cryptography for CryptographicAssumption {
    fn name(&self) -> impl Display {
        match_as_trait!(self =>{
            Self::PRF(x) | Self::AEnc(x) | Self::XOr(x) | Self::DDH(x) => { format!("{}", x.name()) },
            Self::NoGuessingTh => { "no-guessing".to_string() },
            Self::Undefined => { "undefined".to_string() }
        })
    }

    fn add_prelude(&self, pbl: &Problem, sink: &mut impl SmtSink<MSmtParam>) {
        match self {
            Self::NoGuessingTh => add_no_guessing_smt(pbl, sink),
            Self::PRF(x) => x.add_prelude(pbl, sink),
            Self::AEnc(x) => x.add_prelude(pbl, sink),
            Self::XOr(x) => x.add_prelude(pbl, sink),
            Self::DDH(x) => x.add_prelude(pbl, sink),
            Self::Undefined => {}
        }
    }

    fn ref_from_assumption(r: &CryptographicAssumption) -> Option<&Self> {
        Some(r)
    }

    fn register_at(self, _: &mut Problem, _: usize) -> anyhow::Result<&Self> {
        unimplemented!("Calling this is a mistake")
    }

    fn register_nonce(
        &self,
        pbl: &mut ProblemState,
        variables: Vec<Variable>,
        n: Formula,
    ) -> anyhow::Result<()> {
        match_as_trait!(self =>{
            Self::PRF(x) | Self::AEnc(x) | Self::XOr(x) | Self::DDH(x) => { x.register_nonce(pbl, variables, n) },
            _ => {bail!("unsupported for {}", self.name())}
        })
    }
}
