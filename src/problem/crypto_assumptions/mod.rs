// mod euf_cma_mac;
// mod euf_cma_sign;
// mod int_ctxt;
// mod nonce;

use crate::{
    formula::{formula::RichFormula, function::Function},
    smt::{
        macros::seq,
        smt::{Smt, SmtFormula},
        writer::Ctx,
    },
};

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
            _ => todo!()
        }
    }
}

fn aux(m: &SmtFormula, f: &RichFormula) -> SmtFormula {
    seq!(m.clone(), SmtFormula::from(f))
}
