use std::marker::PhantomData;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    tmp: PhantomData<&'bump ()>,
}
