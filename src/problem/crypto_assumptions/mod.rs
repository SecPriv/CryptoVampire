// mod euf_cma_mac;
// mod euf_cma_sign;
// mod int_ctxt;
mod nonce;

pub use nonce::SubtermNonce as SubtermNonce;

use std::rc::Rc;

use crate::formula::{
    file_descriptior::{axioms::Axiom, declare::Declaration},
    formula::RichFormula,
    function::Function,
    variable::Variable,
};

use super::{
    cell::{Assignement, MemoryCell},
    step::Step,
};

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption<'bump> {
    EufCmaMac {
        /// mac(Message, Key) -> Signature
        mac: Function<'bump>,
        /// verify(Signature, Message, Key) -> bool
        verify: Function<'bump>,
    },
    EufCmaSign {
        /// sign(Message, Key) -> Signature
        sign: Function<'bump>,
        /// verify(Signature, Message, vKey) -> bool
        verify: Function<'bump>,
        pk: Function<'bump>,
    },
    IntCtxtSenc {
        enc: Function<'bump>,
        dec: Function<'bump>,
        fail: Function<'bump>,
        verify: Function<'bump>,
    },
    Nonce,
}

impl<'bump> CryptoAssumption<'bump> {
    pub(crate) fn generate_file(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        // ctx: &mut Ctx,
    ) {
        match self {
            // CryptoAssumption::EufCmaMac { mac, verify } => {
            //     euf_cma_mac::generate(assertions, declarations, ctx, mac, verify)
            // }
            // CryptoAssumption::Nonce => nonce::generate(assertions, declarations, ctx),
            // CryptoAssumption::EufCmaSign { sign, verify, pk } => {
            //     euf_cma_sign::generate(assertions, declarations, ctx, sign, verify, pk)
            // }
            // CryptoAssumption::IntCtxtSenc {
            //     enc,
            //     dec,
            //     verify,
            //     fail,
            // } => int_ctxt::generate(assertions, declarations, ctx, enc, dec, verify, fail),
            _ => todo!(),
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Provenance<'bump, T> {
    Plain {
        candidate: T,
    },
    InputPlain {
        step: Step<'bump>,
        candidate: T,
    },
    /// Found `candidate` in `assgnm` while looking into `step`
    InputCell {
        steps: Rc<[Step<'bump>]>,
        assgnm: &'bump Assignement<'bump>,
        cell: MemoryCell<'bump>,
        // call_arg: &'pbl [&'pbl RichFormula],
        // call_t_arg: &'pbl RichFormula,
        candidate: T,
    },
    CellPlain {
        // call_arg: &'pbl [&'pbl RichFormula],
        call_t_arg: &'bump RichFormula<'bump>,
        assgnm: &'bump Assignement<'bump>,
        cell: MemoryCell<'bump>,
        candidate: T,
    },
    /// Found `candidate` in `assgnm` while looking into `step`
    CellDeep {
        // call_arg: &'pbl [&'pbl RichFormula],
        steps: Rc<[Step<'bump>]>,
        call_t_arg: &'bump RichFormula<'bump>,
        assgnm: &'bump Assignement<'bump>,
        cell: MemoryCell<'bump>,
        candidate: T,
    },
    CellInput {
        steps: Rc<[Step<'bump>]>,
        step: Step<'bump>,
        call_t_arg: &'bump RichFormula<'bump>,
        // call_arg: &'pbl [&'pbl RichFormula],
        // call_t_arg: &'pbl RichFormula,
        candidate: T,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
struct DijBranch<'bump> {
    /// extra variables required to express `content`
    vars: Vec<Variable<'bump>>,
    guard: Box<RichFormula<'bump>>,
    content: Box<RichFormula<'bump>>,
}

impl<'pbl, T> Provenance<'pbl, T> {
    pub fn candidate(&self) -> &T {
        match self {
            Provenance::Plain { candidate }
            | Provenance::CellInput { candidate, .. }
            | Provenance::InputPlain { candidate, .. }
            | Provenance::InputCell { candidate, .. }
            | Provenance::CellPlain { candidate, .. }
            | Provenance::CellDeep { candidate, .. } => candidate,
        }
    }
}
