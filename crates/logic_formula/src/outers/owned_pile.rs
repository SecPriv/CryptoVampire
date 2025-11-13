use std::iter::FusedIterator;

use super::*;
/// A pile that owns its formulas and uses an iterator to process them.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct OwnedPile<F, I> {
    pile: Vec<F>,
    iterator: I,
}

/// A type alias for `OwnedPile` used for iterators.
#[allow(private_interfaces)]
pub type OwnedIter<F, I> =
    OwnedPile<Content<<I as FormulaIterator<F>>::U, F, <I as FormulaIterator<F>>::Passing>, I>;

impl<F, I> OwnedPile<F, I> {
    /// Creates a new `OwnedPile`.
    pub fn new(pile: Vec<F>, iterator: I) -> Self {
        Self { pile, iterator }
    }

    /// Returns a mutable reference to the pile as a `RefPile`.
    pub fn as_mut(&mut self) -> RefPile<'_, F, ()> {
        let Self {
            ref mut pile,
            iterator: _,
        } = self;
        RefPile::new(pile, ())
    }
}

impl<F, Passing, I, U> Iterator for OwnedPile<Content<U, F, Passing>, I>
where
    F: AsFormula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
    /// The type of the items yielded by the iterator.
    type Item = I::U;

    /// Advances the iterator and returns the next value.
    fn next(&mut self) -> Option<Self::Item> {
        let nxt = self.pile.pop()?;
        match nxt {
            Content::Resutl(r) => Some(r),
            Content::Next { formula, passing } => {
                let Self { pile, iterator } = self;
                let mut helper = RefPile::new_no_iter(pile);
                iterator.next(formula, passing, &mut helper);
                self.next()
            }
        }
    }
}

impl<F, Passing, I, U> FusedIterator for OwnedPile<Content<U, F, Passing>, I>
where
    F: AsFormula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
}
