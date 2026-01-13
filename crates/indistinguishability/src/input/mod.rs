use std::borrow::Cow;

use log::trace;
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
use crate::terms::{
    AliasRewrite, BUILTINS, Formula, Function, Rewrite, SCHEME_PREFIX, SORT_LIST, Signature, Sort,
    Variable,
};

pub(crate) mod golgge_rules;
pub(crate) mod prelude;
pub(crate) mod shared_cryptography;
pub(crate) mod shared_exists;
// pub(crate) mod shared_fdst;
pub(crate) mod shared_problem;
// pub(crate) mod var;

/// A trait for types that can be registered with the Steel VM.
pub(crate) trait Registerable {
    /// Registers the type and its associated functions with the given `BuiltInModule`.
    fn register(module: &mut BuiltInModule) -> &mut BuiltInModule;
}

/// Registers all `Registerable` types with the given `BuiltInModule`.
pub fn register(module: &mut BuiltInModule) -> &mut BuiltInModule {
    Sort::register(module);
    Function::register(module);
    AliasRewrite::register(module);
    ShrExists::register(module);
    Rewrite::register(module);
    Rule::register(module);
    ShrProblem::register(module);
    Signature::register(module);
    Formula::register(module);
    ShrCrypto::register(module);
    // ShrFindSuchThat::register(module);
    Variable::register(module);
    Report::register(module);
    Configuration::register(module);

    module.register_fn("println!", |x: SteelVal| println!("dbg: {x:?}"));

    module
}

/// Initializes a new Steel `Engine` with the cryptovampire prelude and configuration.
pub fn init_engine(config: Configuration) -> Engine {
    let mut engine = Engine::new();
    engine.add_search_directory(std::env::current_dir().unwrap());

    match config.prelude_version {
        prelude::Preludes::V1 => {
            let mut module = BuiltInModule::new("cryptovampire");

            if !config.no_steel_prelude {
                engine.compile_and_run_raw_program(steel::PRELUDE).unwrap();
            }

            let prelude = config.get_prelude();

            crate::register(&mut module);
            module.register_value(
                "default-config",
                IntoSteelVal::into_steelval(config).unwrap(),
            );
            engine.register_module(module);

            log::trace!("prelude:\n{}", prelude);
            match engine.compile_and_run_raw_program(Cow::Borrowed(prelude)) {
                Ok(_) => (),
                Err(e) => panic!("{}", e.emit_result_to_string("CV_PRELUDE", prelude)),
            };

            engine
        }
        p @ prelude::Preludes::V2 => {
            let mut module = BuiltInModule::new("cryptovampire");
            crate::register(&mut module);
            module.register_value("cli-config", IntoSteelVal::into_steelval(config).unwrap());
            engine.register_module(module);

            let prelude = {
                let mut mkdefintions: String = "\n".into();
                let mut mkexports: String = "\n".into();

                for f in BUILTINS {
                    let name = &f.name;
                    // let old_name = format!("__pre_{}", f.name);
                    mkdefintions += &format!(
                        "(define {name} (register-function cv-{SCHEME_PREFIX}{}))\n",
                        f.name
                    );

                    mkexports += &format!("{name}\n");
                }

                for s in SORT_LIST {
                    mkdefintions += &format!("(define {s} cv-{s})\n");
                    mkexports += &format!("{s}\n");
                }

                p.get_prelude()
                    .replace("@@@EXPORTS@@@", &mkexports)
                    .replace("@@@DEFINITIONS@@@", &mkdefintions)
            };
            trace!("predlue:\n{prelude}");

            engine.register_steel_module("cryptovampire/v2".into(), prelude);

            engine
        }
    }
}

fn conversion_err<To>() -> ::steel::SteelErr {
    use ::steel::*;
    SteelErr::new(
        rerrs::ErrorKind::ConversionError,
        format!("couldn't convert to {}", ::std::any::type_name::<To>()),
    )
}
