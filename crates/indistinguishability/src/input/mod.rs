use steel::steel_vm::builtin::BuiltInModule;

use crate::input::shared_problem::ShrProblem;


pub(crate) mod shared_problem;
pub(crate) mod shared_exists;
pub(crate) mod var;


pub(crate) trait Registerable {
  fn register(module: &mut BuiltInModule) -> &mut BuiltInModule;
}

fn register(module: &mut BuiltInModule) {
  // ShrProblem::
}

fn convert_var(var: egg::Var) -> u32 {
  match var.expose() {
    egg::VarExposed::Sym(_) => unimplemented!(),
    egg::VarExposed::Num(i) => i,
  }
}