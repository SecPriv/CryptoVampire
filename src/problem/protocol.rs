use std::{
    cell::{OnceCell, RefCell},
    rc::Rc,
};

use itertools::Itertools;

use crate::{
    formula::{formula::ARichFormula, variable::Variable},
    implvec,
};

use super::{
    cell::{Assignement, MemoryCell},
    cell_dependancies::graph::DependancyGraph,
    step::Step,
    subterm::FormlAndVars,
};

/// A protocol
#[derive(Debug, Clone)]
pub struct Protocol<'bump> {
    /// This is the graph of various dependancies
    /// between memorycells and steps.
    ///
    /// We talk about dependancies in the sense that
    /// if `A(...)` appears in the step `B` or in an
    /// assignement of the cell `B`, then `B` "depends"
    /// on `A`
    graph: DependancyGraph<'bump>,
    /// the [Step]s
    ///
    /// `init` should be the first step
    steps: Vec<Step<'bump>>,
    /// the [MemoryCell]s
    memory_cells: Vec<MemoryCell<'bump>>,
    /// Extra ordering information between steps
    ordering: Vec<ARichFormula<'bump>>,
    max_var: OnceCell<usize>,
}

pub struct ProtocolStruct<'a, 'bump> {
    pub graph: &'a DependancyGraph<'bump>,
    pub steps: &'a [Step<'bump>],
    pub memory_cells: &'a [MemoryCell<'bump>],
    pub ordering: &'a [ARichFormula<'bump>],
}

impl<'bump> Protocol<'bump> {
    /// favor [Vec] for the iterators
    pub fn new(
        steps: implvec!(Step<'bump>),
        cells: implvec!(MemoryCell<'bump>),
        ordering: implvec!(ARichFormula<'bump>),
    ) -> Self {
        let mut steps = steps.into_iter().collect_vec();
        let memory_cells = cells.into_iter().collect_vec();
        let ordering = ordering.into_iter().collect_vec();
        let graph = DependancyGraph::new(steps.clone(), memory_cells.iter().cloned());

        {
            // make the init step the first one
            let i = steps
                .iter()
                .position(|s| s.is_init_step())
                .expect("no init step !");
            steps.swap(0, i);
        }

        Self {
            graph,
            steps,
            memory_cells,
            ordering,
            max_var: OnceCell::new(),
        }
    }

    pub fn list_top_level_terms<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'bump ARichFormula<'bump>> + 'a
    where
        'bump: 'a,
    {
        self.steps
            .iter()
            .flat_map(|s| [s.condition_arc(), s.message_arc()].into_iter())
            .chain(self.memory_cells.iter().flat_map(|c| {
                c.assignements()
                    .iter()
                    .map(|Assignement { content, .. }| content)
            }))
    }
    pub fn list_top_level_terms_short_lifetime<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'a ARichFormula<'bump>> + 'a
    where
        'bump: 'a,
    {
        self.steps
            .iter()
            .flat_map(|s| [s.condition_arc(), s.message_arc()].into_iter())
            .chain(self.memory_cells.iter().flat_map(|c| {
                c.assignements()
                    .iter()
                    .map(|Assignement { content, .. }| content)
            }))
    }

    pub fn list_top_level_terms_short_lifetime_and_bvars<'a>(
        &'a self,
    ) -> impl Iterator<Item = FormlAndVars<'bump>> + 'a {
        itertools::chain!(
            self.steps.iter().flat_map(|s| {
                let vars: Rc<[_]> = s.free_variables().iter().cloned().collect();
                [s.condition_arc(), s.message_arc()]
                    .map(|t| FormlAndVars::new(Rc::clone(&vars), t.shallow_copy()))
            }),
            self.memory_cells.iter().flat_map(|c| {
                c.assignements()
                    .iter()
                    .map(|Assignement { content, step, .. }| {
                        FormlAndVars::new(
                            step.free_variables().iter().cloned().collect(),
                            content.shallow_copy(),
                        )
                    })
            })
        )
    }

    pub fn max_var(&self) -> usize {
        *self.max_var.get_or_init(|| {
            self.steps()
                .iter()
                .flat_map(|s| s.occuring_variables())
                .chain(
                    self.memory_cells()
                        .iter()
                        .flat_map(|c| c.assignements().iter().flat_map(|a| a.fresh_vars.iter())),
                )
                .map(|v| v.id)
                .max()
                .unwrap_or(0)
        })+1
    }

    pub fn init_step(&self) -> Step<'bump> {
        *self.steps.first().unwrap()
    }

    pub fn graph(&self) -> &DependancyGraph<'bump> {
        &self.graph
    }

    pub fn steps(&self) -> &[Step<'bump>] {
        self.steps.as_ref()
    }

    pub fn memory_cells(&self) -> &[MemoryCell<'bump>] {
        self.memory_cells.as_ref()
    }

    pub fn ordering(&self) -> &[ARichFormula<'bump>] {
        self.ordering.as_ref()
    }

    pub fn as_struct(&self) -> ProtocolStruct<'_, 'bump> {
        let Protocol {
            graph,
            steps,
            memory_cells,
            ordering,
            ..
        } = self;
        ProtocolStruct {
            graph,
            steps,
            memory_cells,
            ordering,
        }
    }

    pub fn is_statefull(&self) -> bool {
        !self.is_stateless()
    }

    pub fn is_stateless(&self) -> bool {
        self.memory_cells().is_empty()
    }
}
