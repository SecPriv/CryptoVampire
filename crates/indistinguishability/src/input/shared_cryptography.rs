use std::ops::{Deref, DerefMut};

use steel::SteelErr;
use steel::rerrs::ErrorKind;
use steel::rvals::Result as SResult;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::Problem;
use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::libraries::{AEnc, DDH, PRF, XOr};
use crate::terms::{
    CryptographicAssumption, Cryptography, Formula, Function, NONCE, Sort, Variable,
};

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

    #[allow(dead_code)]
    fn get_crypto(&self) -> impl Deref<Target = CryptographicAssumption> {
        std::sync::RwLockReadGuard::<'_, Problem>::map(self.pbl.0.read().unwrap(), |pbl| {
            &pbl.cryptography()[self.index]
        })
    }

    fn init_prf(self, hash: Function) {
        let mut pbl = self.pbl.borrow_mut();
        PRF::new_and_add(&mut pbl, self.index, hash);
    }

    fn init_aenc(self, enc: Function, dec: Function, pk: Function) {
        let mut pbl = self.pbl.borrow_mut();
        AEnc::new_and_add(&mut pbl, self.index, enc, dec, Some(pk));
    }

    fn init_senc(self, enc: Function, dec: Function) {
        let mut pbl = self.pbl.borrow_mut();
        AEnc::new_and_add(&mut pbl, self.index, enc, dec, None);
    }

    fn init_xor(self, xor: Function) {
        let mut pbl = self.pbl.borrow_mut();
        XOr::new_and_add(&mut pbl, self.index, xor);
    }

    fn init_ddh(self, g: Function, exp: Function) {
        let mut pbl = self.pbl.borrow_mut();
        DDH::new_and_add(&mut pbl, self.index, g, exp);
    }

    fn register_fresh_nonce(self, variables: Vec<Variable>, n: Formula) -> SResult<()> {
        if let Some(i) = variables.iter().position(|x| {
            !matches!(
                x.get_sort(),
                Some(Sort::Index) | Some(Sort::Time) | Some(Sort::Protocol)
            )
        }) {
            return SResult::Err(SteelErr::new(
                ErrorKind::TypeMismatch,
                format!(
                    "the {}th variable should have sort Index, Time or Protocol",
                    i + 1
                ),
            ));
        }

        let n = match n {
            Formula::App { head, args } if head == NONCE => args[0].clone(),
            x if x.try_get_sort() == Some(Sort::Nonce) => x,
            _ => {
                return SResult::Err(SteelErr::new(
                    ErrorKind::TypeMismatch,
                    format!("{n} isn't a nonce"),
                ));
            }
        };

        let mut pbl = self.pbl.0.write().unwrap();
        let Problem {
            cryptography,
            state,
            ..
        } = pbl.deref_mut();

        match cryptography[self.index].register_nonce(state, variables, n) {
            Err(e) => SResult::Err(SteelErr::new(ErrorKind::Generic, e.to_string())),
            _ => Ok(()),
        }
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
            .register_fn("register-fresh-nonce", Self::register_fresh_nonce)
    }
}
