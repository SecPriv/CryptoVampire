use std::cell::{Ref, RefMut};
use std::ops::Deref;

use itertools::Itertools;
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;

use crate::input::Registerable;
use crate::input::shared_problem::ShrProblem;
use crate::input::var::SVar;
use crate::terms::{Exists, Function, RecFOFormula};

#[derive(Debug, Clone, Steel)]
pub struct ShrExists {
    pub(crate) pbl: ShrProblem,
    pub(crate) index: usize,
}

impl ShrExists {
    fn exists(&self) -> Ref<'_, Exists> {
        Ref::map(self.pbl.borrow(), |x| &x.function.quantifiers()[self.index])
    }

    fn exists_mut(&self) -> RefMut<'_, Exists> {
        RefMut::map(self.pbl.borrow_mut(), |x| {
            x.function.get_mut_quantifier(self.index)
        })
    }

    fn get_vars(&self) -> Vec<SVar> {
        println!("{:?}", &self.exists().vars);
        self.exists().vars.iter().copied().map_into().collect()
    }

    fn get_bound_var(&self) -> SVar {
        self.exists().bound_var.into()
    }

    fn get_tlf(&self) -> Function {
        self.exists().tlf.clone()
    }

    fn get_skolem(&self) -> Function {
        self.exists().skolem.clone()
    }

    fn get_patt(&self) -> RecFOFormula {
        self.exists().patt.deref().into()
    }

    fn set_patt(&self, patt: RecFOFormula) -> ::steel::rvals::Result<()> {
        self.exists_mut().patt = patt.steel_maybe_as_recexp()?;
        Ok(())
    }
}

impl Registerable for ShrExists {
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module)
            .register_fn("exists-vars", Self::get_vars)
            .register_fn("exists-bound-var", Self::get_bound_var)
            .register_fn("get-exists-tlf", Self::get_tlf)
            .register_fn("get-exists-skolem", Self::get_skolem)
            .register_fn("get-exists-pattern", Self::get_patt)
            .register_fn("set-exists-pattern", Self::set_patt)
    }
}
