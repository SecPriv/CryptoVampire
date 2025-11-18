use std::cell::{Ref, RefMut};

use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::shared_problem::ShrProblem;
use crate::input::{Registerable, conversion_err};
use crate::terms::{FindSuchThat, Formula, Function, QuantifierIndex, QuantifierT, Variable};

/// Represents a shared `FindSuchThat` quantifier context within the Steel VM.
#[derive(Debug, Clone, Steel)]
pub struct ShrFindSuchThat {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrFindSuchThat {
    /// Returns the `QuantifierIndex` for this shared `FindSuchThat` quantifier.
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

    /// Returns a vector of the context variables of the `FindSuchThat` quantifier.
    fn get_cvars(&self) -> Vec<Variable> {
        self.fdst().cvars().to_vec()
    }

    /// Returns a vector of the bound variables of the `FindSuchThat` quantifier.
    fn get_bvars(&self) -> Vec<Variable> {
        self.fdst().bvars().to_vec()
    }

    /// Returns the top-level function of the `FindSuchThat` quantifier.
    fn get_tlf(&self) -> Function {
        self.fdst().top_level_function().clone()
    }

    /// Returns a vector of the skolem functions of the `FindSuchThat` quantifier.
    fn get_skolems(&self) -> Vec<Function> {
        self.fdst().skolems().to_vec()
    }

    /// Returns the condition of the `FindSuchThat` quantifier.
    fn get_condition(&self) -> ::steel::rvals::Result<Formula> {
        self.fdst().condition().cloned().ok_or(cerr())
    }

    /// Returns the then-branch of the `FindSuchThat` quantifier.
    fn get_then_branch(&self) -> ::steel::rvals::Result<Formula> {
        self.fdst().then_branch().cloned().ok_or(cerr())
    }

    /// Returns the else-branch of the `FindSuchThat` quantifier.
    fn get_else_branch(&self) -> ::steel::rvals::Result<Formula> {
        self.fdst().else_branch().cloned().ok_or(cerr())
    }

    /// Sets the condition of the `FindSuchThat` quantifier.
    fn set_condition(&self, p: Formula) {
        self.fdst_mut().set_condition(p);
    }

    /// Sets the then-branch of the `FindSuchThat` quantifier.
    fn set_then_branch(&self, p: Formula) {
        self.fdst_mut().set_then_branch(p);
    }

    /// Sets the else-branch of the `FindSuchThat` quantifier.
    fn set_else_branch(&self, p: Formula) {
        self.fdst_mut().set_else_branch(p);
    }
}

impl Registerable for ShrFindSuchThat {
    /// Registers the `ShrFindSuchThat` type and its associated functions with the Steel VM.
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

fn cerr() -> ::steel::SteelErr {
    conversion_err::<Formula>()
}
