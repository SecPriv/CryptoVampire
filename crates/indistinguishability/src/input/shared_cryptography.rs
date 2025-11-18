use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::libraries::{AEnc, DDH, PRF, XOr};
use crate::terms::Function;

/// Represents a shared cryptographic context within the Steel VM.
#[derive(Debug, Clone, Steel)]
pub struct ShrCrypto {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrCrypto {
    fn new(pbl: ShrProblem) -> Self {
        let [index] = pbl.borrow_mut().extend_cryptography();
        Self { pbl, index }
    }

    fn init_prf(self, hash: Function) {
        let mut pbl = self.pbl.borrow_mut();
        PRF::new_and_add(&mut pbl, self.index, hash);
    }

    fn init_aenc(self, enc: Function, dec: Function, pk: Function) {
        let mut pbl = self.pbl.borrow_mut();
        AEnc::new_and_add(&mut pbl, self.index, enc, dec, pk);
    }

    fn init_senc(self, enc: Function, dec: Function, pk: Function) {
        todo!()
    }

    fn init_xor(self, xor: Function) {
        let mut pbl = self.pbl.borrow_mut();
        XOr::new_and_add(&mut pbl, self.index, xor);
    }

    fn init_ddh(self, g: Function, exp: Function) {
        let mut pbl = self.pbl.borrow_mut();
        DDH::new_and_add(&mut pbl, self.index, g, exp);
    }
}

impl Registerable for ShrCrypto {
    /// Registers the `ShrCrypto` type and its associated functions with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("declare-cryptography", Self::new)
            .register_fn("initialize-as-prf", Self::init_prf)
            .register_fn("initialize-as-aenc", Self::init_aenc)
            .register_fn("initialize-as-senc", Self::init_senc)
            .register_fn("initialize-as-xor", Self::init_xor)
            .register_fn("initialize-as-ddh", Self::init_ddh)
    }
}
