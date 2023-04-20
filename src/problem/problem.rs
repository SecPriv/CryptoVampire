use std::{cell::RefCell, rc::Rc};

use crate::{
    container::Container,
    formula::{formula::RichFormula, function::{Function, evaluate::Evaluator, term_algebra::name::NameCaster}, variable::Variable, sort::Sort},
};

use super::protocol::Protocol;

#[derive(Debug, Clone)]
pub struct Problem<'bump> {
    container: &'bump Container<'bump>,
    pub functions: Vec<Function<'bump>>, // to keep track of 'static functions
    pub sorts: Vec<Sort<'bump>>,     // same
    pub evaluator: Rc<Evaluator<'bump>>,
    pub name_caster: Rc<NameCaster<'bump>>,
    pub protocol: Protocol<'bump>,
    pub assertions: Vec<RichFormula<'bump>>,
    pub query: Box<RichFormula<'bump>>,
}

impl<'bump> Problem<'bump> {
    pub fn list_top_level_terms<'a>(&'a self) -> impl Iterator<Item = &'a RichFormula<'bump>>
    where
        'bump: 'a,
    {
        self.assertions
            .iter()
            .chain(std::iter::once(self.query.as_ref()))
            .chain(self.protocol.list_top_level_terms_shot_lifetime())
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
