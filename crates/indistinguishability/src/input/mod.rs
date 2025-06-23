use steel::steel_vm::builtin::BuiltInModule;

use crate::{
    input::{golgge_rules::Rule, shared_exists::ShrExists, shared_problem::ShrProblem},
    terms::{AliasRewrite, Function, Rewrite, Sort},
};

pub(crate) mod golgge_rules;
pub(crate) mod shared_exists;
pub(crate) mod shared_problem;
pub(crate) mod var;

pub(crate) trait Registerable {
    fn register(module: &mut BuiltInModule) -> &mut BuiltInModule;
}

pub fn register(module: &mut BuiltInModule) -> &mut BuiltInModule {
    Sort::register(module);
    Function::register(module);
    AliasRewrite::register(module);
    ShrExists::register(module);
    Rewrite::register(module);
    Rule::register(module);
    ShrProblem::register(module);

    module
}

fn convert_var(var: egg::Var) -> u32 {
    match var.expose() {
        egg::VarExposed::Sym(_) => unimplemented!(),
        egg::VarExposed::Num(i) => i,
    }
}
