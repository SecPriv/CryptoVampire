use crate::{Formula, FormulaIterator, IteratorHelper};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Content<U, F, Passing> {
    Resutl(U),
    Next { formula: F, passing: Passing },
}

impl<U, F, P> From<(F, P)> for Content<U, F, P> {
    fn from((formula, passing): (F, P)) -> Self {
        Content::Next { formula, passing }
    }
}

pub use ref_pile::*;
mod ref_pile;

pub use owned_pile::*;
mod owned_pile;

mod ref_cell_pile;
pub use ref_cell_pile::*;
