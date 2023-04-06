use std::cell::RefCell;

use crate::{
    container::Container,
    formula::{formula::RichFormula, function::Function, variable::Variable},
};

use super::protocol::Protocol;

#[derive(Debug, Clone)]
pub struct Problem<'bump> {
    container: &'bump Container<'bump>,
    pub functions: Vec<Function<'bump>>, // to keep track of 'static functions
    pub sorts: Vec<Function<'bump>>,     // same
    pub protocol: Protocol<'bump>,
    pub assertions: Vec<RichFormula<'bump>>,
    pub query: Box<RichFormula<'bump>>,
}

impl<'bump> Problem<'bump> {
    pub fn max_var(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.protocol
            .list_top_level_terms()
            .chain(self.assertions.iter())
            .chain(std::iter::once(self.query.as_ref()))
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| *id)
            .max()
            .unwrap_or(0)
    }
}
