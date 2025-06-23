use cryptovampire_smt::{Smt, SmtFormula};
use logic_formula::egg::{SimplLang, SimplLangVar};
use std::{io::Write, u128};
use steel::steel_vm::{builtin::BuiltInModule, engine::Engine};
use terms::{Function, Sort};

// ~~~~~~~~~~~~~~~~ macros ~~~~~~~~~~~~~~~~~~

/// Declares a `tr` macro scopped to `name`
///
/// `declare_trace($"test")` expands to
///
/// ```
/// macro_rules! tr {
///     ($($arg:tt)+) => {
///         ::log::trace!(target:"test", $($arg)+)
///     };
/// }
/// ```
/// **NB**: the extra `$` is needed
macro_rules! declare_trace {
    ($dolar:tt$name:literal) => {
        macro_rules! tr {
                                                    ($dolar($arg:tt )+) => {
                                                        ::log::trace!(target: $name, $dolar($arg)+)
                                                    };
                                                }
    };
}

// ~~~~~~~~~~~~~~~ modules ~~~~~~~~~~~~~~~~~~

pub mod problem;
pub use problem::Problem;
pub(crate) mod input;
pub mod protocol;
pub mod rules;
pub mod terms; // <- first for macros
#[cfg(test)]
mod test;
pub(crate) mod utils;
pub(crate) mod vampire;
pub use input::register;
mod configuration;
pub use configuration::Configuration;

// ~~~~~~ type aliases and constants ~~~~~~~~

/// Our global analysis type
pub type N = ();

pub static SIZE: usize = 3;
pub type Lang = SimplLang<Function, SIZE>;
pub type LangVar = SimplLangVar<Function, SIZE>;

pub type MSmtFormula = SmtFormula<Sort, Function>;
pub type MSmt = Smt<Sort, Function>;

// ~~~~~~~~~~~~~~~~ other ~~~~~~~~~~~~~~~~~~~

pub fn init_logger() {
    env_logger::Builder::new()
        .format(|buf, record| {
            if record.file().map(|s| s.contains("egg")) != Some(true) {
                let str = record.args().to_string().replace("\n", "\n\t");
                writeln!(
                    buf,
                    "[{}] in {}:{}\n\t{}",
                    record.level(),
                    record.file().unwrap_or("unknown"),
                    record.line().unwrap_or(0),
                    str
                )
            } else {
                Ok(())
            }
        })
        .parse_default_env()
        .init();
}

pub fn init_engine() -> Engine {
    let mut engine = Engine::new();
    engine.compile_and_run_raw_program(steel::PRELUDE).unwrap();
    let mut module = BuiltInModule::new("cryptovampire");

    crate::register(&mut module);
    engine.register_module(module);
    engine
}
