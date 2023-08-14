mod euf_cma_mac;
mod euf_cma_sign;
mod int_ctxt;
mod nonce;

pub use nonce::SubtermNonce;

pub use euf_cma_mac::{
    SubtermEufCmaMacKey, SubtermEufCmaMacMain, EUF_CMA_MAC_SIGNATURE, EUF_CMA_VERIFY_SIGNATURE,
};

pub use euf_cma_sign::{
    SubtermEufCmaSignKey, SubtermEufCmaSignMain, EUF_CMA_PK_SIGNATURE, EUF_CMA_SIGN_SIGNATURE,
};

pub use int_ctxt::{
    SubtermIntCtxtKey, SubtermIntCtxtMain, SubtermIntCtxtRand, INT_CTXT_DEC_SIGNATURE,
    INT_CTXT_ENC_SIGNATURE, INT_CTXT_VERIFY_SIGNATURE,
};

use crate::environement::environement::Environement;
use crate::formula::{
    file_descriptior::{axioms::Axiom, declare::Declaration},
    formula::RichFormula,
    function::Function,
    variable::Variable,
};

pub use self::euf_cma_mac::EufCmaMac;
pub use self::euf_cma_sign::EufCmaSign;
pub use self::nonce::Nonce;

use super::generator::Generator;
use super::problem::Problem;

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption<'bump> {
    EufCmaMac(EufCmaMac<'bump>),
    EufCmaSign(EufCmaSign<'bump>),
    IntCtxtSenc {
        enc: Function<'bump>,
        dec: Function<'bump>,
        fail: Function<'bump>,
        verify: Function<'bump>,
    },
    Nonce(Nonce),
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
            CryptoAssumption::EufCmaMac(euf) => euf.generate(assertions, declarations, env, pbl),
            CryptoAssumption::EufCmaSign(euf) => euf.generate(assertions, declarations, env, pbl),
            CryptoAssumption::IntCtxtSenc {
                enc: _,
                dec: _,
                fail: _,
                verify: _,
            } => todo!(),
            CryptoAssumption::Nonce(nonce) => nonce.generate(assertions, declarations, env, pbl),
        }
    }
}

// fn aux<T, U>(ctx: &T, a: U, b: U) -> U
// where
//     T: FormulaUser<U>,
// {
//     // seq!(m.clone(), SmtFormula::from(f))
//     ctx.eqf(a, b)
// }

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
// enum Provenance<'bump, T> {
//     Plain {
//         candidate: T,
//     },
//     InputPlain {
//         step: Step<'bump>,
//         candidate: T,
//     },
//     /// Found `candidate` in `assgnm` while looking into `step`
//     InputCell {
//         steps: Rc<[Step<'bump>]>,
//         assgnm: &'bump Assignement<'bump>,
//         cell: MemoryCell<'bump>,
//         // call_arg: &'pbl [&'pbl RichFormula],
//         // call_t_arg: &'pbl RichFormula,
//         candidate: T,
//     },
//     CellPlain {
//         // call_arg: &'pbl [&'pbl RichFormula],
//         call_t_arg: &'bump RichFormula<'bump>,
//         assgnm: &'bump Assignement<'bump>,
//         cell: MemoryCell<'bump>,
//         candidate: T,
//     },
//     /// Found `candidate` in `assgnm` while looking into `step`
//     CellDeep {
//         // call_arg: &'pbl [&'pbl RichFormula],
//         steps: Rc<[Step<'bump>]>,
//         call_t_arg: &'bump RichFormula<'bump>,
//         assgnm: &'bump Assignement<'bump>,
//         cell: MemoryCell<'bump>,
//         candidate: T,
//     },
//     CellInput {
//         steps: Rc<[Step<'bump>]>,
//         step: Step<'bump>,
//         call_t_arg: &'bump RichFormula<'bump>,
//         // call_arg: &'pbl [&'pbl RichFormula],
//         // call_t_arg: &'pbl RichFormula,
//         candidate: T,
//     },
// }

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
struct DijBranch<'bump> {
    /// extra variables required to express `content`
    vars: Vec<Variable<'bump>>,
    guard: Box<RichFormula<'bump>>,
    content: Box<RichFormula<'bump>>,
}

// impl<'pbl, T> Provenance<'pbl, T> {
//     pub fn candidate(&self) -> &T {
//         match self {
//             Provenance::Plain { candidate }
//             | Provenance::CellInput { candidate, .. }
//             | Provenance::InputPlain { candidate, .. }
//             | Provenance::InputCell { candidate, .. }
//             | Provenance::CellPlain { candidate, .. }
//             | Provenance::CellDeep { candidate, .. } => candidate,
//         }
//     }
// }
