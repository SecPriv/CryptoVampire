mod searcher;
mod tptp;
mod vampire;
pub use vampire::{VampireArg,  VampireExec  };

mod runner;
pub use runner::{Discoverer, Runner, RunnerBase, RunnerOut, RunnerOutI, Runners};
