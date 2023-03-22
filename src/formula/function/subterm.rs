use std::marker::PhantomData;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Subterm<'bump> {
    tmp: PhantomData<&'bump ()>,
}


fn enlarge<'a, 'b>(q: Subterm<'a>) -> Subterm<'b> where 'a:'b {
    q
}