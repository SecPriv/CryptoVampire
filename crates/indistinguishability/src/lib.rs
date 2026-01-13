#![feature(mapped_lock_guards)]
#![feature(type_alias_impl_trait)]

use std::io::Write;

use cryptovampire_smt::{Smt, SmtFormula, SmtParam};
use golgge::Program;
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

/// Defines the problem structure and related functionalities.
pub mod problem;
pub use problem::Problem;
/// Handles the parsing and processing of input files.
pub(crate) mod input;
/// Contains the rules for the e-graph rewriting system.
pub mod libraries;
/// Handles the definition and manipulation of cryptographic protocols.
pub mod protocol;
/// Defines the different runners for executing cryptographic analysis.
pub(crate) mod runners;
/// Defines the terms and their operations used in the cryptographic analysis.
pub mod terms; // <- first for macros
/// Contains utility functions and helpers.
pub(crate) mod utils;
/// Re-exports functions for initializing the engine and registering input handlers.
pub use input::{init_engine, register};
/// Defines the configuration structures for the crate.
mod configuration;
/// Re-exports the main Configuration structure for the crate.
pub use configuration::{Commands, Configuration};

use crate::problem::{PAnalysis, RcRule};
use crate::terms::Variable;

// ~~~~~~ type aliases and constants ~~~~~~~

/// Our global analysis type
///
/// This is currently unused
/// Our global analysis type
///
/// This is currently unused
pub type N = ();

/// The language of the e-graph
/// The language of the e-graph
pub type Lang = terms::InnerLang;
/// A variable or a node in the e-graph
/// A variable or a node in the e-graph
pub type LangVar = egg::ENodeOrVar<Lang>;

/// The parameter for the SMT solver
///
/// This is a marker struct that implements the `SmtParam` trait.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MSmtParam;

/// A formula in the SMT solver
/// A formula in the SMT solver
pub type MSmtFormula = SmtFormula<MSmtParam>;
/// The SMT solver
/// The SMT solver
pub type MSmt = Smt<MSmtParam>;

pub type CVProgram<'a, R = RcRule> = Program<Lang, PAnalysis<'a>, R>;

// ~~~~~~~~~~~~~~~~ other ~~~~~~~~~~~~~~~~~~~

/// Initializes the logger
///
/// This function sets up the logger to format messages in a specific way.
/// It also filters out messages from the `egg` crate.
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
    /// The function type for the SMT solver
    type Function = Function;

    /// The sort type for the SMT solver
    type Sort = Sort;

    /// The variable type for the SMT solver
    type SVar = Variable;
}
