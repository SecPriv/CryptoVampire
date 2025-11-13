use std::iter::FusedIterator;

use super::*;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RefPile<'a, F, I> {
    pile: &'a mut Vec<F>,
    iterator: I,
}

impl<'a, F, I> RefPile<'a, F, I> {
    pub fn new(pile: &'a mut Vec<F>, iterator: I) -> Self {
        Self { pile, iterator }
    }
}

impl<'a, F> RefPile<'a, F, ()> {
    pub fn new_no_iter(pile: &'a mut Vec<F>) -> Self {
        Self { pile, iterator: () }
    }
}

impl<'a, U, F, Passing, I> IteratorHelper for RefPile<'a, Content<U, F, Passing>, I>
where
    F: AsFormula,
{
    type F = F;
    type U = U;

    type Passing = Passing;

    fn extend_child(
        &mut self,
        iter: impl IntoIterator<Item = (Self::F, Self::Passing)>,
    ) -> &mut Self {
        self.pile.extend(iter.into_iter().map(Into::into));
        self
    }

    fn extend_result(&mut self, results: impl IntoIterator<Item = Self::U>) -> &mut Self {
        self.pile.extend(results.into_iter().map(Content::Resutl));
        self
    }
}

impl<'a, U, F, Passing, I> Iterator for RefPile<'a, Content<U, F, Passing>, I>
where
    F: AsFormula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
    type Item = I::U;

    fn next(&mut self) -> Option<Self::Item> {
        let nxt = self.pile.pop()?;
        match nxt {
            Content::Resutl(r) => Some(r),
            Content::Next { formula, passing } => {
                let Self { pile, iterator } = self;
                let mut helper = RefPile::new_no_iter(*pile);
                iterator.next(formula, passing, &mut helper);
                self.next()
            }
        }
    }
}

impl<'a, U, F, Passing, I> FusedIterator for RefPile<'a, Content<U, F, Passing>, I>
where
    F: AsFormula,
    I: FormulaIterator<F, Passing = Passing, U = U>,
{
}
