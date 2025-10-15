use std::cell::{Ref, RefMut};

use itertools::Itertools;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::terms::{Exists, Function, QuantifierIndex, QuantifierT, RecFOFormula, Variable};

#[derive(Debug, Clone, Steel)]
pub struct ShrExists {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrExists {
    pub fn index(&self) -> QuantifierIndex {
        QuantifierIndex {
            temporary: false,
            index: self.index,
        }
    }

    fn exists(&self) -> Ref<'_, Exists> {
        Ref::map(self.pbl.borrow(), |pbl| {
            Exists::try_from_ref(self.index().get(pbl.functions()).unwrap()).unwrap()
        })
    }

    fn exists_mut(&self) -> RefMut<'_, Exists> {
        RefMut::map(self.pbl.borrow_mut(), |pbl| {
            Exists::try_from_mut(self.index().get_mut(pbl.functions_mut()).unwrap()).unwrap()
        })
    }

    fn get_cvars(&self) -> Vec<Variable> {
        self.exists().cvars().to_vec()
    }

    fn get_bvars(&self) -> Vec<Variable> {
        self.exists().bvars().to_vec()
    }

    fn get_tlf(&self) -> Function {
        self.exists().top_level_function().clone()
    }

    fn get_skolems(&self) -> Vec<Function> {
        self.exists().skolems().to_vec()
    }

    fn get_patt(&self) -> RecFOFormula {
        self.exists().patt().unwrap().clone()
    }

    fn set_patt(&self, patt: RecFOFormula) -> ::steel::rvals::Result<()> {
        self.exists_mut().set_patt(patt);
        Ok(())
    }
}

impl Registerable for ShrExists {
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
