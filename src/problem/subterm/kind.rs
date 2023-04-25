use crate::environement::environement::Environement;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub enum SubtermKind {
    Regular,
    Vampire,
}

impl<'a, 'bump> From<&'a Environement<'bump>> for SubtermKind {
    fn from(env: &'a Environement<'bump>) -> Self {
        if env.use_vampire_subterm() {
            Self::Vampire
        } else {
            Self::default()
        }
    }
}

impl Default for SubtermKind {
    fn default() -> Self {
        Self::Regular
    }
}
