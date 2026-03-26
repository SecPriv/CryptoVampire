use std::ops::{Deref, DerefMut};
use std::sync::{MutexGuard, RwLockReadGuard, RwLockWriteGuard};

use log::trace;
use steel::SteelVal;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::builtin::BuiltInModule;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::terms::{Exists, Formula, Function, QuantifierIndex, QuantifierT, Variable};

/// Represents a shared existential quantifier context within the Steel VM.
#[derive(Debug, Clone, Steel)]
pub struct ShrExists {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrExists {
    /// Returns the `QuantifierIndex` for this shared existential quantifier.
    pub fn index(&self) -> QuantifierIndex {
        QuantifierIndex {
            temporary: false,
            index: self.index,
        }
    }

    fn exists(&self) -> impl Deref<Target = Exists> {
        self.exists_mut()
    }

    fn exists_mut(&self) -> impl DerefMut<Target = Exists> {
        MutexGuard::map(self.pbl.0.lock().unwrap(), |pbl| {
            Exists::try_from_mut(self.index().get_mut(pbl.functions_mut()).unwrap()).unwrap()
        })
    }
}

/// Returns a vector of the context variables of the existential quantifier.
#[steel_derive::declare_steel_function(name = "get-cvars")]
fn get_cvars(shre: ShrExists) -> Vec<Variable> {
    shre.exists().cvars().to_vec()
}

/// Returns a vector of the bound variables of the existential quantifier.
#[steel_derive::declare_steel_function(name = "get-bvars")]
fn get_bvars(shre: ShrExists) -> Vec<Variable> {
    shre.exists().bvars().to_vec()
}

/// Returns the top-level function of the existential quantifier.
#[steel_derive::declare_steel_function(name = "get-tlf")]
fn get_tlf(shre: ShrExists) -> Function {
    shre.exists().top_level_function().clone()
}

/// Returns a vector of the skolem functions of the existential quantifier.
#[steel_derive::declare_steel_function(name = "get-skolem")]
fn get_skolems(shre: ShrExists) -> Vec<Function> {
    shre.exists().skolems().to_vec()
}

/// Returns the pattern of the existential quantifier. (deprecated)
#[steel_derive::declare_steel_function(name = "get-exists-pattern")]
fn get_patt(shre: ShrExists) -> Formula {
    shre.exists().patt().unwrap().clone()
}

/// Sets the pattern of the existential quantifier.
#[steel_derive::declare_steel_function(name = "set-exists-pattern")]
fn set_patt(shre: ShrExists, patt: Formula) -> ::steel::rvals::Result<SteelVal> {
    shre.exists_mut().set_patt(patt);
    ().into_steelval()
}

impl Registerable for ShrExists {
    fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
        let name = "crypotvampire/ll/exists";
        let mut module = BuiltInModule::new(name);
        module
            .register_type::<Self>("Exists?")
            .register_native_fn_definition(GET_CVARS_DEFINITION)
            .register_native_fn_definition(GET_BVARS_DEFINITION)
            .register_native_fn_definition(GET_TLF_DEFINITION)
            .register_native_fn_definition(GET_SKOLEMS_DEFINITION)
            .register_native_fn_definition(GET_PATT_DEFINITION)
            .register_native_fn_definition(SET_PATT_DEFINITION);

        trace!("defined {name} scheme module");
        assert!(modules.insert(name.into(), module).is_none());
    }
}
