use std::cell::RefCell;

use crate::Problem;
use crate::runners::SmtRunner;
use crate::terms::{Formula, Function};

mod smt;
pub use smt::{Context, SmtCache};

#[derive(Default)]
pub struct Cache {
    pub vampire_exec: Option<SmtRunner>,
    pub smt: SmtCache,

    /// a cache for the quantifiers
    pub quantifier_cache: Vec<(Formula, Function)>,
}

impl Problem {
    pub fn get_or_init_smt_runner(&mut self) -> &SmtRunner {
        if self.cache.vampire_exec.is_none() {
            self.cache.vampire_exec = Some(SmtRunner::new(self));
        };

        self.cache.vampire_exec.as_ref().unwrap()
    }
}
