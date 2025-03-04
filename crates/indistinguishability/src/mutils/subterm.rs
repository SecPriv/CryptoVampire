use egg::{Analysis, EClass, EGraph, Id, Language};
use rustc_hash::FxHashSet;
use utils::implvec;

#[derive(Debug, Clone)]
pub struct SubtermIterator<'a, L: Language, N: Analysis<L>> {
    todo: Vec<&'a EClass<L, N::Data>>,
    done: FxHashSet<Id>,
    egraph: &'a EGraph<L, N>,
}

impl<'a, L: Language, N: Analysis<L>> Iterator for SubtermIterator<'a, L, N> {
    type Item = &'a EClass<L, N::Data>;

    fn next(&mut self) -> Option<Self::Item> {
        let eclass = self.todo.pop()?;
        if self.done.contains(&eclass.id) {
            return self.next();
        }
        self.todo.extend(
            eclass
                .iter()
                .flat_map(|l| l.children().iter())
                .map(|id| &self.egraph[*id]),
        );
        self.done.insert(eclass.id);
        Some(eclass)
    }
}

impl<'a, L: Language, N: Analysis<L>> SubtermIterator<'a, L, N> {
    pub fn new_many_eclass(
        egraph: &'a EGraph<L, N>,
        eclasses: implvec!(&'a EClass<L, N::Data>),
    ) -> Self {
        Self {
            todo: eclasses.into_iter().collect(),
            done: Default::default(),
            egraph,
        }
    }

    pub fn new_many_id(egraph: &'a EGraph<L, N>, ids: implvec!(Id)) -> Self {
        Self::new_many_eclass(egraph, ids.into_iter().map(|id| &egraph[id]))
    }

    pub fn new(egraph: &'a EGraph<L, N>, start: Id) -> Self {
        Self::new_many_id(egraph, [start])
    }

    pub fn clear_with_eclasses(&mut self, eclasses: implvec!(&'a EClass<L, N::Data>)) {
        self.done.clear();
        self.todo.clear();
        self.todo.extend(eclasses);
    }

    pub fn clear_with_ids(&mut self, ids: implvec!(Id)) {
        self.clear_with_eclasses(ids.into_iter().map(|id| &self.egraph[id]));
    }

    pub fn clear(&mut self, start: Id) {
        self.clear_with_ids([start]);
    }
}
