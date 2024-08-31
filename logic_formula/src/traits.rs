use crate::{outers::OwnedPile, Destructed, Head};

pub trait Formula: Sized {
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

    fn iter_with<I>(self, iter: I, init: I::Passing) -> impl Iterator<Item = I::U>
    where
        I: FormulaIterator<F = Self>,
        Self: Clone,
    {
        let mut pile = OwnedPile::new(iter);
        pile.as_mut().push_child(self, init);
        pile
    }
}

pub trait IteratorHelper {
    type F: Formula;
    type Passing;
    type U;

    fn push_result(&mut self, result:Self::U) -> &mut Self {
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

pub trait FormulaIterator {
    type F: Formula;
    type Passing;

    type U;

    fn next<H>(&mut self, current: Self::F, passing: &Self::Passing, helper: &mut H)
    where
        H: IteratorHelper<F = Self::F, Passing = Self::Passing, U=Self::U>;
}


pub trait Bounder<Var> {

  fn bounds(&self) -> impl Iterator<Item = Var>;
}