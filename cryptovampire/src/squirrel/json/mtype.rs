use super::Content;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
pub enum SortKind {
    Large,
    NameFixedLength,
    Finite,
    Fixed,
    WellFounded,
    Enum,
}

impl SortKind {
    pub fn can_be_index(&self) -> bool {
        match self {
            SortKind::Finite | SortKind::Fixed | SortKind::Enum => true,
            _ => false,
        }
    }
}

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SortData(pub Vec<SortKind>);

impl SortData {
    pub fn can_be_index(&self) -> bool {
        self.0.iter().all(|k| k.can_be_index())
    }
}
pub type Sort<'a> = Content<'a, SortData>;
