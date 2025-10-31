use std::collections::BTreeMap;

use static_init::dynamic;

use super::Function;
use super::builtin::NAME_TO_MESSAGE;
use crate::formula::formula::ARichFormula;
use crate::formula::sort::builtins::MESSAGE;
use crate::formula::sort::{FOSort, Sort};
use crate::formula::utils::Applicable;

#[dynamic]
pub static DEFAULT_NAME_CASTER: NameCasterCollection<'static> = NameCasterCollection {
    content: [(MESSAGE.as_sort().into(), *NAME_TO_MESSAGE)]
        .into_iter()
        .collect(),
};

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct NameCasterCollection<'bump> {
    content: BTreeMap<FOSort<'bump>, Function<'bump>>,
}

impl<'bump> NameCasterCollection<'bump> {
    pub fn new(content: BTreeMap<FOSort<'bump>, Function<'bump>>) -> Self {
        Self { content }
    }

    pub fn cast_function(&self, sort: &Sort<'bump>) -> Option<&Function<'bump>> {
        self.content.get(&sort.as_fo())
    }

    pub fn cast<F>(&self, sort: Sort<'bump>, f: F) -> ARichFormula<'bump>
    where
        ARichFormula<'bump>: From<F>,
    {
        self.cast_function(&sort).unwrap().f([f])
    }

    pub fn content_mut(&mut self) -> &mut BTreeMap<FOSort<'bump>, Function<'bump>> {
        &mut self.content
    }
}

impl<'bump> FromIterator<(Sort<'bump>, Function<'bump>)> for NameCasterCollection<'bump> {
    fn from_iter<T: IntoIterator<Item = (Sort<'bump>, Function<'bump>)>>(iter: T) -> Self {
        Self {
            content: iter.into_iter().map(|(s, f)| (s.into(), f)).collect(),
        }
    }
}
