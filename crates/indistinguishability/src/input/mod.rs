use steel::{
    SteelVal,
    steel_vm::{builtin::BuiltInModule, engine::Engine, register_fn::RegisterFn},
};

use crate::{
    input::{
        golgge_rules::Rule, shared_cryptography::ShrCrypto, shared_exists::ShrExists,
        shared_problem::ShrProblem,
    },
    terms::{AliasRewrite, Function, RecFOFormula, Rewrite, Signature, Sort},
};

pub(crate) mod golgge_rules;
pub(crate) mod shared_cryptography;
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
    Signature::register(module);
    RecFOFormula::register(module);
    ShrCrypto::register(module);

    module.register_fn("println!", |x: SteelVal| println!("dbg: {x:?}"));

    module
}

fn convert_var(var: egg::Var) -> u32 {
    match var.expose() {
        egg::VarExposed::Sym(_) => unimplemented!(),
        egg::VarExposed::Num(i) => i,
    }
}

static CV_PRELUDE: &str = include_str!("./prelude.scm");

pub fn init_engine() -> Engine {
    let mut engine = Engine::new();
    let mut module = BuiltInModule::new("cryptovampire");
    engine.compile_and_run_raw_program(steel::PRELUDE).unwrap();

    crate::register(&mut module);
    engine.register_module(module);
    match engine.compile_and_run_raw_program(CV_PRELUDE) {
        Ok(_) => (),
        Err(e) => panic!("{}", e.emit_result_to_string("CV_PRELUDE", CV_PRELUDE)),
    };

    engine
}
