use std::{marker::PhantomData, rc::Rc, fmt::Debug};

use crate::problem::subterm::{Subterm as PblSubterm, traits::SubtermAux, AsSubterm};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Subterm<'bump> {
    Nope(PhantomData<&'bump ()>)
}


fn enlarge<'a, 'b>(q: Subterm<'a>) -> Subterm<'b> where 'a:'b {
    q
}