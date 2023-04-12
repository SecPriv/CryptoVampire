use std::collections::HashMap;

use crate::formula::{formula::RichFormula, function::Function, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Name<'bump> {
    name: String,
    target: Sort<'bump>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NameCaster<'bump> {
    content: HashMap<Sort<'bump>, Function<'bump>>,
}

impl<'bump> NameCaster<'bump> {
    pub fn cast_function(&self, sort: &Sort<'bump>) -> Option<&Function<'bump>> {
        self.content.get(&sort)
    }

    pub fn cast(&self, sort: Sort<'bump>, f: RichFormula<'bump>) -> RichFormula<'bump> {
        self.cast_function(&sort).unwrap().f([f])
    }
}
