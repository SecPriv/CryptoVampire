use utils::impossible::Impossible;

use crate::iterators::{FreeVariableIterator, UsedVariableIterator};
use crate::outers::{Content, OwnedIter, OwnedPile};
use crate::{Destructed, Head};

pub trait AsFormula: Sized {
    type Var;
    type Fun;
    type Quant;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>>;

    fn head(self) -> Head<Self> {
        self.destruct().head
    }

    fn args(self) -> impl Iterator<Item = Self> {
        self.destruct().args
    }

    #[allow(private_interfaces)]
    fn iter_with<I>(self, iter: I, init: I::Passing) -> OwnedIter<Self, I>
    where
        I: FormulaIterator<Self>,
    {
        Vec::new().with(self, iter, init)
    }

    fn free_vars_iter(self) -> impl Iterator<Item = Self::Var>
    where
        Self::Quant: Bounder<Self::Var>,
        Self::Var: Eq + Clone,
    {
        self.iter_with(FreeVariableIterator::default(), 0)
    }

    fn used_vars_iter(self) -> impl Iterator<Item = Self::Var>
    where
        Self::Var: Eq + Clone,
    {
        self.iter_with(UsedVariableIterator, ())
    }
}

pub trait IteratorHelper {
    type F: AsFormula;
    type Passing;
    type U;

    fn push_result(&mut self, result: Self::U) -> &mut Self {
        self.extend_result([result])
    }

    fn extend_result(&mut self, results: impl IntoIterator<Item = Self::U>) -> &mut Self;

    fn push_child(&mut self, child: Self::F, passing: Self::Passing) -> &mut Self {
        self.extend_child([(child, passing)])
    }

    fn extend_child(
        &mut self,
        iter: impl IntoIterator<Item = (Self::F, Self::Passing)>,
    ) -> &mut Self;

    fn extend_child_same_passing(
        &mut self,
        iter: impl IntoIterator<Item = Self::F>,
        passing: &Self::Passing,
    ) -> &mut Self
    where
        Self::Passing: Clone,
    {
        self.extend_child(iter.into_iter().map(|arg| (arg, passing.clone())))
    }

    fn extend_child_with_default(&mut self, iter: impl IntoIterator<Item = Self::F>) -> &mut Self
    where
        Self::Passing: Default,
    {
        self.extend_child(iter.into_iter().map(|arg| (arg, Default::default())))
    }
}

pub trait FormulaIterator<F: AsFormula> {
    type Passing;

    type U;

    fn next<H>(&mut self, current: F, passing: Self::Passing, helper: &mut H)
    where
        H: IteratorHelper<F = F, Passing = Self::Passing, U = Self::U>;
}

pub trait Bounder<Var> {
    fn bounds(&self) -> impl Iterator<Item = Var>;
}

impl<V> Bounder<V> for Impossible {
    fn bounds(&self) -> impl Iterator<Item = V> {
        [].into_iter()
    }
}

pub trait IteratorContainer<F, I>
where
    F: AsFormula,
    I: FormulaIterator<F>,
{
    type Iter: Iterator<Item = I::U>;
    fn with(self, formula: F, iterator: I, init: I::Passing) -> Self::Iter;
}

impl<F, I> IteratorContainer<F, I> for Vec<Content<I::U, F, I::Passing>>
where
    F: AsFormula,
    I: FormulaIterator<F>,
{
    type Iter = OwnedIter<F, I>;

    fn with(mut self, formula: F, iterator: I, init: I::Passing) -> Self::Iter {
        self.clear();
        let mut pile = OwnedPile::new(self, iterator);
        pile.as_mut().push_child(formula, init);
        pile
    }
}
