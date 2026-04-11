use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::MSmtFormula;
use crate::terms::{Formula, Function};

#[derive(Debug)]
pub struct Context {
    pub query: Formula,
    /// `query` but already in smt form
    pub query_smt: MSmtFormula<'static>,
    pub using_cache: bool,
}

#[derive(Debug, Default)]
pub struct SmtCache {
    repeating_runs: Arc<()>,

    /// see [Problem::try_translate]
    pub(crate) occured_quantfiers: RefCell<FxHashSet<Function>>,
}

impl SmtCache {
    pub fn lock(&self) -> impl Drop + use<> {
        self.repeating_runs.clone()
    }

    pub fn anything_cached(&self) -> bool {
        !self.occured_quantfiers.borrow().is_empty()
    }

    pub fn reset(&mut self) {
        if Arc::strong_count(&self.repeating_runs) <= 1 {
            self.occured_quantfiers.get_mut().clear();
        }
    }

    pub fn force_reset(&mut self) {
        assert!(Arc::strong_count(&self.repeating_runs) <= 1);
        self.occured_quantfiers.get_mut().clear();
    }
}
