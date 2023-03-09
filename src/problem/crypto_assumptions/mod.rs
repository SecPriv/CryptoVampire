mod euf_cma_mac;
// mod euf_cma_sign;
mod int_ctxt;
mod nonce;

use std::rc::Rc;

use crate::{
    formula::{
        formula::{RichFormula, Variable},
        formula_user::FormulaUser,
        function::Function,
    },
    smt::{smt::Smt, writer::Ctx},
};

use super::{cell::{Assignement, MemoryCell}, step::Step};

// should be quick to copy
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum CryptoAssumption {
    EufCmaMac {
        /// mac(Message, Key) -> Signature
        mac: Function,
        /// verify(Signature, Message, Key) -> bool
        verify: Function,
    },
    EufCmaSign {
        /// sign(Message, Key) -> Signature
        sign: Function,
        /// verify(Signature, Message, vKey) -> bool
        verify: Function,
        pk: Function,
    },
    IntCtxtSenc {
        enc: Function,
        dec: Function,
        fail: Function,
        verify: Function,
    },
    Nonce,
}

impl CryptoAssumption {
    pub(crate) fn generate_smt(
        &self,
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &mut Ctx,
    ) {
        match self {
            CryptoAssumption::EufCmaMac { mac, verify } => {
                euf_cma_mac::generate(assertions, declarations, ctx, mac, verify)
            }
            CryptoAssumption::Nonce => nonce::generate(assertions, declarations, ctx),
            // CryptoAssumption::EufCmaSign { sign, verify, pk } => {
            //     euf_cma_sign::generate(assertions, declarations, ctx, sign, verify, pk)
            // }
            CryptoAssumption::IntCtxtSenc {
                enc,
                dec,
                verify,
                fail,
            } => int_ctxt::generate(assertions, declarations, ctx, enc, dec, verify, fail),
            _ => todo!(),
        }
    }
}

fn aux<T, U>(ctx: &T, a: U, b: U) -> U
where
    T: FormulaUser<U>,
{
    // seq!(m.clone(), SmtFormula::from(f))
    ctx.eqf(a, b)
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
enum Provenance<'pbl, T> {
    Plain {
        candidate: T,
    },
    InputPlain {
        step: &'pbl Step,
        candidate: T,
    },
    /// Found `candidate` in `assgnm` while looking into `step`
    InputCell {
        steps: Rc<[&'pbl Step]>,
        assgnm: &'pbl Assignement,
        cell: &'pbl MemoryCell,
        // call_arg: &'pbl [&'pbl RichFormula],
        // call_t_arg: &'pbl RichFormula,
        candidate: T,
    },
    CellPlain {
        // call_arg: &'pbl [&'pbl RichFormula],
        call_t_arg: &'pbl RichFormula,
        assgnm: &'pbl Assignement,
        cell: &'pbl MemoryCell,
        candidate: T,
    },
    /// Found `candidate` in `assgnm` while looking into `step`
    CellDeep {
        // call_arg: &'pbl [&'pbl RichFormula],
        steps: Rc<[&'pbl Step]>,
        call_t_arg: &'pbl RichFormula,
        assgnm: &'pbl Assignement,
        cell: &'pbl MemoryCell,
        candidate: T,
    },
    CellInput {
        steps: Rc<[&'pbl Step]>,
        step: &'pbl Step,
        call_t_arg: &'pbl RichFormula,
        // call_arg: &'pbl [&'pbl RichFormula],
        // call_t_arg: &'pbl RichFormula,
        candidate: T,
    },
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
struct DijBranch {
    /// extra variables required to express `content`
    vars: Vec<Variable>,
    guard: Box<RichFormula>,
    content: Box<RichFormula>,
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
