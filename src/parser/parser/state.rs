use crate::environement::traits::{KnowsRealm, Realm, RealmMerger};

use super::parsing_environement::Environement;

#[derive(Debug, Clone, Copy)]
pub struct State<'a, 'str, 'bump>(RealmMerger<Realm, &'a Environement<'bump, 'str>>);

impl<'a, 'str, 'bump> From<&'a Environement<'bump, 'str>> for State<'a, 'str, 'bump> {
    fn from(value: &'a Environement<'bump, 'str>) -> Self {
        Self(RealmMerger {
            inner: Default::default(),
            outer: value,
        })
    }
}

impl<'a, 'str, 'bump> KnowsRealm for State<'a, 'str, 'bump> {
    fn get_realm(&self) -> Realm {
        self.0.get_realm()
    }
}

impl<'a, 'str, 'bump> State<'a, 'str, 'bump> {
    pub fn to_low(&self) -> Self {
        Self(RealmMerger {
            inner: Realm::Evaluated,
            ..self.0
        })
    }
    pub fn to_high(&self) -> Self {
        Self(RealmMerger {
            inner: Realm::Symbolic,
            ..self.0
        })
    }
    pub fn to_evaluated(&self) -> Self {
        self.to_low()
    }
    pub fn to_symbolic(&self) -> Self {
        self.to_high()
    }
    pub fn to_realm(&self, realm: &impl KnowsRealm) -> Self {
        Self(RealmMerger {
            inner: realm.get_realm(),
            ..self.0
        })
    }
}
