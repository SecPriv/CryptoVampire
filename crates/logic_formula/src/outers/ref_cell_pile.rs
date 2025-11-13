use std::cell::{RefCell, RefMut};
use std::iter::FusedIterator;

use super::*;
/// A pile that holds a mutable reference to a `Vec<F>` and uses an iterator to process its contents.
#[derive(Debug)]
pub struct RefCellPile<'a, F, I> {
    pile: RefMut<'a, Vec<F>>,
    iterator: I,
}

impl<'a, F, I> RefCellPile<'a, F, I> {
    /// Creates a new `RefCellPile` from a `RefCell<Vec<F>>`.
    pub fn new(pile: &'a RefCell<Vec<F>>, iterator: I) -> Self {
        Self::new_mut(pile.borrow_mut(), iterator)
    }
    /// Creates a new `RefCellPile` from a `RefMut<Vec<F>>`.
    pub fn new_mut(pile: RefMut<'a, Vec<F>>, iterator: I) -> Self {
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

    /// Clears the pile.
    pub fn clear(&mut self) {
        self.pile.clear()
    }
}

impl<'a, F, Passing, I, U> Iterator for RefCellPile<'a, Content<U, F, Passing>, I>
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

impl<'a, F, Passing, I, U> FusedIterator for RefCellPile<'a, Content<U, F, Passing>, I>
where
    F: AsFormula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
}
