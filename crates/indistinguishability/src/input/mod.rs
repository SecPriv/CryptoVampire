use rustc_hash::FxHashMap;
use steel::SteelVal;
use steel::rvals::IntoSteelVal;
use steel::steel_vm::builtin::BuiltInModule;
use steel::steel_vm::engine::Engine;
use steel::steel_vm::register_fn::RegisterFn;

use crate::Configuration;
use crate::input::golgge_rules::Rule;
use crate::input::shared_cryptography::ShrCrypto;
use crate::input::shared_exists::ShrExists;
// use crate::input::shared_fdst::ShrFindSuchThat;
use crate::input::shared_problem::ShrProblem;
use crate::problem::Report;
use crate::protocol::{MemoryCell, Step};
use crate::terms::{Alias, Formula, Function, Rewrite, Signature, Sort, Variable, mk_scheme_lib};

pub(crate) mod golgge_rules;
pub(crate) mod shared_cryptography;
pub(crate) mod shared_exists;
// pub(crate) mod shared_fdst;
pub(crate) mod shared_problem;
// pub(crate) mod var;

pub static BASE_LL_MODULE: &str = "cryptovampire/ll";

/// A trait for types that can be registered with the Steel VM.
pub(crate) trait Registerable {
    /// Registers the type and its associated functions with the given `BuiltInModule`.
    fn register(modules: &mut FxHashMap<String, BuiltInModule>);
}

/// Registers all `Registerable` types with the given `BuiltInModule`.
pub fn register() -> FxHashMap<String, BuiltInModule> {
    let mut modules = FxHashMap::default();

    {
        let mut module = BuiltInModule::new(BASE_LL_MODULE);
        module.register_fn("println!", |x: SteelVal| println!("dbg: {x:?}"));
        modules.insert(BASE_LL_MODULE.into(), module);
    }

    Sort::register(&mut modules);
    Function::register(&mut modules);
    Alias::register(&mut modules);
    ShrExists::register(&mut modules);
    Rewrite::register(&mut modules);
    Rule::register(&mut modules);
    ShrProblem::register(&mut modules);
    Signature::register(&mut modules);
    Formula::register(&mut modules);
    ShrCrypto::register(&mut modules);
    // ShrFindSuchThat::register(module);
    Variable::register(&mut modules);
    Report::register(&mut modules);
    Step::register(&mut modules);
    MemoryCell::register(&mut modules);

    modules
}

macro_rules! libraries {
    ($($name:literal ),* $(,)?) => {
        [
            $(
                ($name, include_str!( concat!( "../../scheme/libs/",  $name , ".scm")))
            ),*
        ]
    };
}

/// Initializes a new Steel `Engine` with the cryptovampire prelude and configuration.
pub fn init_engine(config: Configuration) -> Engine {
    let mut engine = Engine::new();
    engine.add_search_directory(config.root_directory.clone().unwrap());

    let mut modules = register();
    modules
        .get_mut(BASE_LL_MODULE)
        .unwrap()
        .register_value("cli-config", IntoSteelVal::into_steelval(config).unwrap());

    for (_, module) in modules {
        engine.register_module(module);
    }

    let libs = libraries![
        "type",
        "sort",
        "signature",
        "function",
        "formula",
        "cryptography",
        "protocol",
        "solver",
        "stdlib"
    ];

    for (name, lib) in libs {
        engine.register_steel_module(format!("cryptovampire/{name}"), lib.into());
    }

    engine.register_steel_module("cryptovampire/builtin-functions".into(), mk_scheme_lib());

    engine
}

fn conversion_err<To>() -> ::steel::SteelErr {
    use ::steel::*;
    SteelErr::new(
        rerrs::ErrorKind::ConversionError,
        format!("couldn't convert to {}", ::std::any::type_name::<To>()),
    )
}
