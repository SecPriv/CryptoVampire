use std::fmt::Debug;
use std::rc::Rc;

use golgge::Dependancy;

use crate::runners::vampire::RegularVampire;
use crate::{MSmtFormula, Problem};

pub(crate) mod vampire;

pub trait SmtSolver: Debug {
    /// Tries to prove .
    ///
    /// ## returns
    /// - `Err(_)` if the solver errored out (e.g., syntax error and such).
    /// - `Ok(None)` the solver didn't manage to prove nor disprove the query
    /// - `Ok(b)` with `b` true is proven, `false` otherwise
    fn try_run(&self, pbl: &mut Problem, query: MSmtFormula) -> anyhow::Result<Option<bool>>;
}

#[derive(Debug, Clone)]
pub struct SmtRunner(Rc<dyn SmtSolver>);

impl SmtRunner {
    pub fn new(pbl: &Problem) -> Self {
        Self(Rc::new(RegularVampire::new(pbl)))
    }

    pub fn run_to_dependancy(&self, pbl: &mut Problem, query: MSmtFormula) -> Dependancy {
        if let Some(true) = self.try_run(pbl, query).unwrap() {
            Dependancy::axiom()
        } else {
            Dependancy::impossible()
        }
    }

    /// TODO: make run many solvers
    pub fn try_run(&self, pbl: &mut Problem, query: MSmtFormula) -> anyhow::Result<Option<bool>> {
        self.0.try_run(pbl, query)
    }
}
