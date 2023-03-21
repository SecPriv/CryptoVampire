use std::marker::PhantomData;

use bumpalo::Bump;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    tmp: PhantomData<&'bump Bump>
}