use std::ops::{Deref, DerefMut};

use log::trace;
use steel::SteelErr;
use steel::rerrs::ErrorKind;
use steel::rvals::Result as SResult;
use steel::steel_vm::builtin::BuiltInModule;
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
}

#[steel_derive::declare_steel_function(name = "declare-cryptography")]
fn declare_crypto(pbl: ShrProblem) -> ShrCrypto {
    ShrCrypto::new(pbl)
}

/// Enable PRF axioms and rules
#[steel_derive::declare_steel_function(name = "init->prf")]
fn init_prf(shrc: ShrCrypto, hash: Function) {
    let mut pbl = shrc.pbl.borrow_mut();
    PRF::new_and_add(&mut pbl, shrc.index, hash);
}

/// Enable asymetric enryption axioms and rules. (i.e., IND-CCA and ENC-KP)
#[steel_derive::declare_steel_function(name = "init->aenc")]
fn init_aenc(shrc: ShrCrypto, enc: Function, dec: Function, pk: Function) {
    let mut pbl = shrc.pbl.borrow_mut();
    AEnc::new_and_add(&mut pbl, shrc.index, enc, dec, Some(pk));
}

/// Enable symetric enryption axioms and rules. (i.e., IND-CCA)
#[steel_derive::declare_steel_function(name = "init->senc")]
fn init_senc(shrc: ShrCrypto, enc: Function, dec: Function) {
    let mut pbl = shrc.pbl.borrow_mut();
    AEnc::new_and_add(&mut pbl, shrc.index, enc, dec, None);
}

/// Enable xor axioms and rules
#[steel_derive::declare_steel_function(name = "init->xor")]
fn init_xor(shrc: ShrCrypto, xor: Function) {
    let mut pbl = shrc.pbl.borrow_mut();
    XOr::new_and_add(&mut pbl, shrc.index, xor);
}

/// Enable ddh axioms and rules
#[steel_derive::declare_steel_function(name = "init->ddh")]
fn init_ddh(shrc: ShrCrypto, g: Function, exp: Function) {
    let mut pbl = shrc.pbl.borrow_mut();
    DDH::new_and_add(&mut pbl, shrc.index, g, exp);
}

/// Register a nonce to the various routines that spawn fresh nonces. This can
/// be usefull for things like PRF, ENC-KP or DDH to unify to a user-defined
/// nonce, instead of a fully fresh one.
#[steel_derive::declare_steel_function(name = "register-fresh-nonce")]
fn register_fresh_nonce(shrc: ShrCrypto, variables: Vec<Variable>, n: Formula) -> SResult<()> {
    if let Some(i) = variables.iter().position(|x| {
        !matches!(
            x.get_sort(),
            Some(Sort::Index) | Some(Sort::Time) | Some(Sort::Protocol)
        )
    }) {
        return SResult::Err(SteelErr::new(
            ErrorKind::TypeMismatch,
            format!(
                "the {}th variable should have sort 'Index', 'Time' or 'Protocol'",
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

    let mut pbl = shrc.pbl.0.write().unwrap();
    let Problem {
        cryptography,
        state,
        ..
    } = pbl.deref_mut();

    match cryptography[shrc.index].register_nonce(state, variables, n) {
        Err(e) => SResult::Err(SteelErr::new(ErrorKind::Generic, e.to_string())),
        _ => Ok(()),
    }
}

impl Registerable for ShrCrypto {
    fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
        let name = "cryptovampire/ll/cryptography";
        let mut module = BuiltInModule::new(name);

        module
            .register_native_fn_definition(INIT_PRF_DEFINITION)
            .register_native_fn_definition(INIT_AENC_DEFINITION)
            .register_native_fn_definition(INIT_SENC_DEFINITION)
            .register_native_fn_definition(INIT_DDH_DEFINITION)
            .register_native_fn_definition(INIT_XOR_DEFINITION)
            .register_native_fn_definition(DECLARE_CRYPTO_DEFINITION)
            .register_native_fn_definition(REGISTER_FRESH_NONCE_DEFINITION);

        trace!("defined {name} scheme module");
        assert!(modules.insert(name.into(), module).is_none())
    }
}
