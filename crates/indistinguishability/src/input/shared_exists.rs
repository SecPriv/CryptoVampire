use std::ops::{Deref, DerefMut};
use std::sync::{RwLockReadGuard, RwLockWriteGuard};

use steel::steel_vm::register_fn::RegisterFn;
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
        RwLockReadGuard::map(self.pbl.0.read().unwrap(), |pbl| {
            Exists::try_from_ref(self.index().get(pbl.functions()).unwrap()).unwrap()
        })
    }

    fn exists_mut(&self) -> impl DerefMut<Target = Exists> {
        RwLockWriteGuard::map(self.pbl.0.write().unwrap(), |pbl| {
            Exists::try_from_mut(self.index().get_mut(pbl.functions_mut()).unwrap()).unwrap()
        })
    }

    /// Returns a vector of the context variables of the existential quantifier.
    fn get_cvars(&self) -> Vec<Variable> {
        self.exists().cvars().to_vec()
    }

    /// Returns a vector of the bound variables of the existential quantifier.
    fn get_bvars(&self) -> Vec<Variable> {
        self.exists().bvars().to_vec()
    }

    /// Returns the top-level function of the existential quantifier.
    fn get_tlf(&self) -> Function {
        self.exists().top_level_function().clone()
    }

    /// Returns a vector of the skolem functions of the existential quantifier.
    fn get_skolems(&self) -> Vec<Function> {
        self.exists().skolems().to_vec()
    }

    /// Returns the pattern of the existential quantifier.
    fn get_patt(&self) -> Formula {
        self.exists().patt().unwrap().clone()
    }

    /// Sets the pattern of the existential quantifier.
    fn set_patt(&self, patt: Formula) -> ::steel::rvals::Result<()> {
        self.exists_mut().set_patt(patt);
        Ok(())
    }
}

impl Registerable for ShrExists {
    /// Registers the `ShrExists` type and its associated functions with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("exists-cvars", Self::get_cvars)
            .register_fn("exists-bvars", Self::get_bvars)
            .register_fn("get-exists-tlf", Self::get_tlf)
            .register_fn("get-exists-skolems", Self::get_skolems)
            .register_fn("get-exists-pattern", Self::get_patt)
            .register_fn("set-exists-pattern", Self::set_patt)
    }
}
