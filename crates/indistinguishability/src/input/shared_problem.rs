use std::{
    any::TypeId,
    cell::{Ref, RefCell, RefMut},
    ops::{Deref, DerefMut},
    rc::Rc,
};

use steel::{rvals::CustomType, steel_vm::register_fn::RegisterFn};
use steel_derive::Steel;

use crate::{input::Registerable, terms::Function, Problem};

#[derive(Debug, Clone, Steel)]
pub struct ShrProblem(Rc<RefCell<Problem>>);

impl ShrProblem {
    pub fn borrow(&self) -> Ref<'_, Problem>{
        self.0.borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<'_, Problem> {
        self.0.borrow_mut()
    }

    /// returns [None] is the shared pointer is still shared
    pub fn try_into_inner(self) -> Option<Problem> {
        Rc::into_inner(self.0).map(RefCell::into_inner)
    }

    // =========================================================
    // ========================= API ===========================
    // =========================================================

    fn register_function_declaration(self, fun: Function) -> Function {
        self.borrow_mut().function.add(fun.clone());
        fun
    }
}

impl Registerable for ShrProblem {
    fn register(module: &mut steel::steel_vm::builtin::BuiltInModule) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module);
        module.register_fn("declare_fun", Self::register_function_declaration);
        module
    }
}