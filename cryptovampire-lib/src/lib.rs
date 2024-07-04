#![recursion_limit = "256"]

pub mod container;
pub mod environement;
pub mod formula;
pub mod problem;
pub mod runner;
pub mod smt;
pub mod subterm;

pub use problem::step::INIT_STEP_NAME;
pub use subterm::kind::SubtermKind;
