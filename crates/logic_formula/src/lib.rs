/// Provides various iterators for traversing formulas.
pub mod iterators;
/// Provides data structures for managing formula iteration.
pub mod outers;
mod traits;

use std::fmt::Debug;
use std::hash::Hash;

pub use head::*;
pub use outers::Content;
pub use traits::*;
mod head;

pub use desctucted::*;
mod desctucted;

#[cfg(feature = "egg")]
/// Provides integration with the `egg` library.
pub mod egg;
