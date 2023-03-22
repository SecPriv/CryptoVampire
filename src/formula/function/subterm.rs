use std::marker::PhantomData;

use crate::formula::container::Container;


#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    tmp: PhantomData<&'bump ()>
}