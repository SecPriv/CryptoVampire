pub mod iterators;
pub mod outers;
mod traits;

use std::{fmt::Debug, hash::Hash};

pub use outers::Content;
pub use traits::*;

pub use head::*;
mod head;

pub use desctucted::*;
mod desctucted;

#[cfg(feature = "egg")]
pub mod egg {
    use std::{fmt::{Debug, Display}, hash::Hash};

    use egg::{ENodeOrVar, Id, Language, RecExpr};

    use crate::Formula;

  #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
  pub struct SimpleLanguage<D> {
    head: D,
    args: Vec<Id>
  }

  impl<D:Display> Display for SimpleLanguage<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.head.fmt(f)
    }
  }

  impl<D> Language for SimpleLanguage<D> where D: Debug+ Clone+Eq+Ord+Hash {
    type Discriminant = D;
  
    fn discriminant(&self) -> Self::Discriminant {
        self.head.clone()
    }
  
    fn matches(&self, other: &Self) -> bool {
        self.discriminant() == other.discriminant() && self.args.len() == other.args.len()
    }
  
    fn children(&self) -> &[Id] {
        &self.args
    }
  
    fn children_mut(&mut self) -> &mut [Id] {
        &mut self.args
    }
  }
}