use super::parsing_environement::Environement;
use crate::environement::traits::{KnowsRealm, Realm, RealmMerger};

#[derive(Debug, Clone, Copy)]
pub struct State<'a, 'str, 'bump, S>(RealmMerger<Realm, &'a Environement<'bump, 'str, S>>);

impl<'a, 'str, 'bump, S> From<&'a Environement<'bump, 'str, S>> for State<'a, 'str, 'bump, S> {
    fn from(value: &'a Environement<'bump, 'str, S>) -> Self {
        Self(RealmMerger {
            inner: Default::default(),
            outer: value,
        })
    }
}

impl<'a, 'str, 'bump, S> KnowsRealm for State<'a, 'str, 'bump, S> {
    fn get_realm(&self) -> Realm {
        self.0.get_realm()
    }
}

impl<'a, 'str, 'bump, S> State<'a, 'str, 'bump, S> {
    #[allow(dead_code)]
    pub fn to_low(&self) -> Self {
        Self(RealmMerger {
            inner: Realm::Evaluated,
            ..self.0
        })
    }
    #[allow(dead_code)]
    pub fn to_high(&self) -> Self {
        Self(RealmMerger {
            inner: Realm::Symbolic,
            ..self.0
        })
    }
    #[allow(dead_code)]
    pub fn to_evaluated(&self) -> Self {
        self.to_low()
    }
    #[allow(dead_code)]
    pub fn to_symbolic(&self) -> Self {
        self.to_high()
    }
    #[allow(dead_code)]
    pub fn to_realm(&self, realm: &impl KnowsRealm) -> Self {
        Self(RealmMerger {
            inner: realm.get_realm(),
            ..self.0
        })
    }
}
