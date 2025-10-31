use std::io::Write;

use cryptovampire_smt::{Smt, SmtFormula, SmtParam};
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
#[rustfmt::skip]
macro_rules! declare_trace {
    ($dolar:tt $name:literal) => {
        #[allow(unused_macros)]
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
pub(crate) mod smt;
pub(crate) mod runners;
pub use input::{init_engine, register};
mod configuration;
pub use configuration::Configuration;

use crate::terms::Variable;

// ~~~~~~ type aliases and constants ~~~~~~~~

/// Our global analysis type
pub type N = ();

pub type Lang = terms::InnerLang;
pub type LangVar = egg::ENodeOrVar<Lang>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MSmtParam;

pub type MSmtFormula = SmtFormula<MSmtParam>;
pub type MSmt = Smt<MSmtParam>;

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

impl SmtParam for MSmtParam {
    type Function = Function;

    type Sort = Sort;

    type SVar = Variable;
}
