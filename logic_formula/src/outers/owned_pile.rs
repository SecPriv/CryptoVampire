use std::iter::FusedIterator;

use super::*;
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct OwnedPile<F, I> {
    pile: Vec<F>,
    iterator: I,
}

pub type OwnedIter<F, I> =
    OwnedPile<Content<<I as FormulaIterator<F>>::U, F, <I as FormulaIterator<F>>::Passing>, I>;

impl<F, I> OwnedPile<F, I> {

    pub fn new(pile: Vec<F>, iterator: I) -> Self {
        Self { pile, iterator }
    }
    
    pub fn as_mut<'a>(&'a mut self) -> RefPile<'a, F, ()> {
        let Self {
            ref mut pile,
            iterator: _,
        } = self;
        RefPile::new(pile, ())
    }
}

impl<F, Passing, I, U> Iterator for OwnedPile<Content<U, F, Passing>, I>
where
    F: Formula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
    type Item = I::U;

    fn next(&mut self) -> Option<Self::Item> {
        let nxt = self.pile.pop()?;
        match nxt {
            Content::Resutl(r) => Some(r),
            Content::Next { formula, passing } => {
                let Self { pile, iterator } = self;
                let mut helper = RefPile::new_no_iter(pile);
                iterator.next(formula, &passing, &mut helper);
                self.next()
            }
        }
    }
}

impl<F, Passing, I, U> FusedIterator for OwnedPile<Content<U, F, Passing>, I>
where
    F: Formula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
}
