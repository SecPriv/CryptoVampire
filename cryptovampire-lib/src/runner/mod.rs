mod searcher;
mod tptp;
mod vampire;
pub use vampire::{
    VampireArg, VampireError, VampireExec, VampireOutput, DEFAULT_VAMPIRE_ARGS,
};

mod runner;
pub use runner::{Runner, RunnerOut, RunnerOutI, RunnerBase};