#[allow(clippy::module_inception)]
mod smt;
pub use smt::{Smt, SmtCons, SmtFile, SmtFormula};

pub const SMT_FILE_EXTENSION: &str = ".smt";
