use egg::{Analysis, EGraph, Id, Language};
use utils::implvec;

#[derive(Debug, Clone)]
pub struct ECallMap<V>(Vec<(Id, V)>);

impl<V> Default for ECallMap<V> {
    fn default() -> Self {
        Self::new([])
    }
}

impl<V> ECallMap<V> {
    pub fn new(i: implvec!((Id, V))) -> Self {
        ECallMap(i.into_iter().collect())
    }

    pub fn get(&self, id: Id) -> Option<&V> {
        self.0
            .iter()
            .filter_map(|(x, v)| (x == &id).then_some(v))
            .next()
    }

    pub fn entry(&mut self, id: Id) -> Entry<'_, V> {
        let tmp = self
            .0
            .iter_mut()
            .filter_map(|(x, v)| (x == &id).then_some(v))
            // safety: `v` is a &mut
            .map(|v| unsafe { std::ptr::NonNull::new_unchecked(v as *mut _) })
            .next();
        match tmp {
            Some(mut value) => Entry::Occupied(OccupiedEntry {
                id,
                // `v` is actually our &mut from above, in this branch it is only aliased by `self`
                value: unsafe { value.as_mut() },
            }),
            None => Entry::Vacant(VacantEntry { map: self, id }),
        }
    }

    fn unchecked_insert(&mut self, id: Id, value: V) -> &mut (Id, V) {
        self.0.push((id, value));
        self.0.last_mut().unwrap()
    }

    pub fn canonicalise<L: Language, N: Analysis<L>>(&mut self, egraph: &EGraph<L, N>) {
        for (id, _) in &mut self.0 {
            let nid = egraph.find(*id);
            *id = nid
        }
    }
}

pub struct VacantEntry<'a, V> {
    map: &'a mut ECallMap<V>,
    id: Id,
}

impl<'a, V> VacantEntry<'a, V> {
    pub fn insert(self, value: V) -> &'a mut V {
        let id = self.id;
        let (_, v) = self.map.unchecked_insert(id, value);
        v
    }
}

pub struct OccupiedEntry<'a, V> {
    id: Id,
    value: &'a mut V,
}

impl<'a, V> OccupiedEntry<'a, V> {
    pub fn get(self) -> &'a mut V {
        self.value
    }
}

pub enum Entry<'a, V> {
    Vacant(VacantEntry<'a, V>),
    Occupied(OccupiedEntry<'a, V>),
}

impl<'a, V> Entry<'a, V> {
    pub fn id(&self) -> Id {
        match self {
            Entry::Vacant(VacantEntry { id, .. })
            | Entry::Occupied(OccupiedEntry { id, .. }) => *id,
        }
    }

    pub fn or_insert_with_key(self, f: impl FnOnce(Id) -> V) -> &'a mut V {
        match self {
            Entry::Vacant(_) => {
                let default = f(self.id());
                self.insert_entry(default)
            }
            Entry::Occupied(occupied_entry) => occupied_entry,
        }
        .value
    }

    pub fn or_inster(self, default: V) -> &'a mut V {
        self.or_insert_with_key(|_| default)
    }

    pub fn insert_entry(self, value: V) -> OccupiedEntry<'a, V> {
        match self {
            Self::Occupied(e) => {
                *e.value = value;
                e
            }
            Self::Vacant(e) => OccupiedEntry {
                id: e.id,
                value: e.insert(value),
            },
        }
    }
}
