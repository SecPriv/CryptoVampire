//! Run smt solver and extract information out of them.
//!
//! This module gather most of the logic concerning executing an smt solver and
//! the possible solver specific code. Through theses files a 'runner' refers to something that can lauch an smt solver
//! and possibly communicate with it.
//!
//! # High overview
//! Given a certain number `n` of tries and a [Problem] `P`, we do:
//! 1. for each runner, generate the appropriate file
//! 2. execute the runner
//! 3. *optionnal*: gather new instances of the crypto axioms
//! 4. if we've been at this step less than `n` times and step `3` brough new
//!    instances, go back to step `1`
//!
//! If we get a positive, negative or unexpected (e.g., syntax error from a solver)
//! we quit with the relevant result as fast as possible.
//!
//! [Problem]: crate::problem::Problem

mod error;
#[allow(clippy::module_inception)]
mod runner;
mod runner_helper;
mod runners;
mod searcher;
mod tptp;
mod vampire;
mod z3;

pub use error::RunnerError;
pub use runner::{Discoverer, Runner, RunnerBase, RunnerHandler, RunnerOut, RunnerOutI};
pub(crate) use runner_helper::*;
pub use runners::{RunnerResult, Runners};
pub use vampire::{VampireArg, VampireExec};
