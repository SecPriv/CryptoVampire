use std::{
    cell::{RefCell, RefMut},
    iter::FusedIterator,
};

use super::*;
#[derive(Debug)]
pub struct RefCellPile<'a, F, I> {
    pile: RefMut<'a, Vec<F>>,
    iterator: I,
}


impl<'a, F, I> RefCellPile<'a, F, I> {
    pub fn new(pile: &'a RefCell<Vec<F>>, iterator: I) -> Self {
        Self {
            pile: pile.borrow_mut(),
            iterator,
        }
    }

    pub fn as_mut<'b>(&'b mut self) -> RefPile<'b, F, ()> {
        let Self {
            ref mut pile,
            iterator: _,
        } = self;
        RefPile::new(pile, ())
    }
}


impl<'a, F, Passing, I, U> Iterator for RefCellPile<'a, Content<U, F, Passing>, I>
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

impl<'a, F, Passing, I, U> FusedIterator for RefCellPile<'a, Content<U, F, Passing>, I>
where
    F: Formula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
}
