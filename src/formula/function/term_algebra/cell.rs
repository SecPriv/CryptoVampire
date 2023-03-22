use std::marker::PhantomData;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Cell<'bump> {
    cell: PhantomData<&'bump ()>,
}
