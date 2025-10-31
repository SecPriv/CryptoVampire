mod cell;
mod euf_cma;
mod int_ctxt;
mod nonce;
mod uf_cma;
mod unfolding;

pub use euf_cma::{
    EUF_CMA_PK_SIGNATURE, EUF_CMA_SIGN_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE, SubtermEufCmaSignKey,
    SubtermEufCmaSignMain,
};
pub use int_ctxt::{
    INT_CTXT_DEC_SIGNATURE, INT_CTXT_ENC_SIGNATURE, INT_CTXT_FAIL_SIGNATURE,
    INT_CTXT_VERIFY_SIGNATURE, SubtermIntCtxtKey, SubtermIntCtxtMain, SubtermIntCtxtRand,
};
use itertools::Itertools;
pub use nonce::SubtermNonce;
pub use uf_cma::{
    SubtermUfCmaKey, SubtermUfCmaMain, UF_CMA_MAC_SIGNATURE, UF_CMA_VERIFY_SIGNATURE, UfCmaBuilder,
};
pub use unfolding::*;
use utils::implvec;

use self::cell::Cell;
pub use self::euf_cma::EufCma;
pub use self::int_ctxt::IntCtxt;
pub use self::nonce::Nonce;
pub use self::uf_cma::UfCma;
use super::generator::Generator;
use super::problem::Problem;
use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption<'bump> {
    UfCma(UfCma<'bump>),
    EufCmaSign(EufCma<'bump>),
    IntCtxtSenc(IntCtxt<'bump>),
    Nonce(Nonce),
    MemoryCell(Cell),
    Unfolding(Unfolding<'bump>),
}

impl<'bump> Generator<'bump> for CryptoAssumption<'bump> {
    fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        match self {
            CryptoAssumption::UfCma(euf) => euf.generate(assertions, declarations, env, pbl),
            CryptoAssumption::EufCmaSign(euf) => euf.generate(assertions, declarations, env, pbl),
            CryptoAssumption::IntCtxtSenc(intctx) => {
                intctx.generate(assertions, declarations, env, pbl)
            }
            CryptoAssumption::Nonce(nonce) => nonce.generate(assertions, declarations, env, pbl),
            CryptoAssumption::MemoryCell(cell) => cell.generate(assertions, declarations, env, pbl),
            CryptoAssumption::Unfolding(u) => u.generate(assertions, declarations, env, pbl),
        }
    }
}

bitflags::bitflags! {
    #[derive(Default, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug )]
    pub struct CryptoFlag: u8 {
        /// Set the crypto to exploit
        const STRONG    = 1 << 0;
        /// Asume it is an Hmac
        const HMAC      = 1 << 1;
        /// Recursive exec macro.
        ///
        /// Use the recursive defintion of exec
        const RECURSIVE_EXEC = 1 << 2;
        /// Quantified exec macro.
        ///
        /// Use the 'exists' equivalent definition of exec.
        /// This is the default, as this doesn't imply recursion
        const DIRECT_EXEC = 1 << 3;
    }
}

impl CryptoFlag {
    /// Similar to [Self::from_name] but it is case insensitive and ors all the names
    pub fn from_names<'a>(names: implvec!(&'a str)) -> Option<Self> {
        names
            .into_iter()
            .map(|n| Self::from_name(&n.to_uppercase()))
            .fold_options(Self::empty(), |acc, x| acc | x)
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;

    use crate::problem::crypto_assumptions::CryptoFlag;

    #[test]
    fn name_test() {
        println!(
            "{}",
            CryptoFlag::STRONG.iter_names().map(|(n, _)| n).join(", ")
        )
    }
}
