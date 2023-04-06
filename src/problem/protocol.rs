use std::cell::RefCell;

use crate::formula::{formula::RichFormula, variable::Variable};

use super::{
    cell::{Assignement, MemoryCell},
    cell_dependancies::graph::DependancyGraph,
    step::Step,
};

#[derive(Debug, Clone)]
pub struct Protocol<'bump> {
    pub graph: DependancyGraph<'bump>,
    pub steps: Vec<Step<'bump>>,
    pub memory_cells: Vec<MemoryCell<'bump>>,
    pub ordering: Vec<RichFormula<'bump>>,
}

impl<'bump> Protocol<'bump> {
    pub fn list_top_level_terms<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'bump RichFormula<'bump>> + 'a
    where
        'bump: 'a,
    {
        self.steps
            .iter()
            .flat_map(|s| [s.condition(), s.message()].into_iter())
            .chain(self.memory_cells.iter().flat_map(|c| {
                c.assignements()
                    .iter()
                    .map(|Assignement { content, .. }| content)
            }))
    }
    pub fn list_top_level_terms_shot_lifetime<'a>(
        &'a self,
    ) -> impl Iterator<Item = &'a RichFormula<'bump>> + 'a
    where
        'bump: 'a,
    {
        self.steps
            .iter()
            .flat_map(|s| [s.condition(), s.message()].into_iter())
            .chain(self.memory_cells.iter().flat_map(|c| {
                c.assignements()
                    .iter()
                    .map(|Assignement { content, .. }| content)
            }))
    }

    pub fn max_var(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.list_top_level_terms()
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| *id)
            .max()
            .unwrap_or(0)
    }
}
