use std::marker::PhantomData;

use bumpalo::Bump;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Cell<'bump> {
    cell: PhantomData<&'bump Bump>
}