use std::cell::{Ref, RefMut};
use std::ops::Deref;

use itertools::Itertools;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::terms::{FindSuchThat, Function, QuantifierIndex, QuantifierT, RecFOFormula, Variable};

#[derive(Debug, Clone, Steel)]
pub struct ShrFindSuchThat {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrFindSuchThat {
    pub fn index(&self) -> QuantifierIndex {
        QuantifierIndex {
            temporary: false,
            index: self.index,
        }
    }

    fn fdst(&self) -> Ref<'_, FindSuchThat> {
        Ref::map(self.pbl.borrow(), |pbl| {
            FindSuchThat::try_from_ref(self.index().get(pbl.functions()).unwrap()).unwrap()
        })
    }

    fn fdst_mut(&self) -> RefMut<'_, FindSuchThat> {
        RefMut::map(self.pbl.borrow_mut(), |pbl| {
            FindSuchThat::try_from_mut(self.index().get_mut(pbl.functions_mut()).unwrap()).unwrap()
        })
    }

    fn get_cvars(&self) -> Vec<Variable> {
        self.fdst().cvars().to_vec()
    }

    fn get_bvars(&self) -> Vec<Variable> {
        self.fdst().bvars().to_vec()
    }

    fn get_tlf(&self) -> Function {
        self.fdst().top_level_function().clone()
    }

    fn get_skolems(&self) -> Vec<Function> {
        self.fdst().skolems().to_vec()
    }

    fn get_condition(&self) -> RecFOFormula {
        self.fdst().condition().into()
    }

    fn get_then_branch(&self) -> RecFOFormula {
        self.fdst().then_branch().into()
    }

    fn get_else_branch(&self) -> RecFOFormula {
        self.fdst().else_branch().into()
    }

    fn set_condition(&self, p: RecFOFormula) -> ::steel::rvals::Result<()> {
        self.fdst_mut().set_condition(p.steel_maybe_as_recexp()?);
        Ok(())
    }

    fn set_then_branch(&self, p: RecFOFormula) -> ::steel::rvals::Result<()> {
        self.fdst_mut().set_then_branch(p.steel_maybe_as_recexp()?);
        Ok(())
    }

    fn set_else_branch(&self, p: RecFOFormula) -> ::steel::rvals::Result<()> {
        self.fdst_mut().set_else_branch(p.steel_maybe_as_recexp()?);
        Ok(())
    }
}

impl Registerable for ShrFindSuchThat {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("find-such-that-cvars", Self::get_cvars)
            .register_fn("find-such-that-bvars", Self::get_bvars)
            .register_fn("get-find-such-that-tlf", Self::get_tlf)
            .register_fn("get-find-such-that-skolems", Self::get_skolems)
            .register_fn("get-find-such-that-condition", Self::get_condition)
            .register_fn("set-find-such-that-condition", Self::set_condition)
            .register_fn("get-find-such-that-then-branch", Self::get_then_branch)
            .register_fn("set-find-such-that-then-branch", Self::set_then_branch)
            .register_fn("get-find-such-that-else-branch", Self::get_else_branch)
            .register_fn("set-find-such-that-else-branch", Self::set_else_branch)
    }
}
