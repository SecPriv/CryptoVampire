use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::rules::PRF;
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
}

impl Registerable for ShrCrypto {
    /// Registers the `ShrCrypto` type and its associated functions with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("declare-cryptography", Self::new)
            .register_fn("initialize-as-prf", Self::init_prf)
    }
}
