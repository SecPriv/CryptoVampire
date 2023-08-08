use crate::formula::{variable::Variable, formula::{RichFormula, ARichFormula}};


pub trait Substitution<'bump> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump>;

    fn apply(&self, f: &RichFormula<'bump>) -> ARichFormula<'bump> {
        match f {
            RichFormula::Var(v) => self.get(v),
            RichFormula::Fun(fun, args) => RichFormula::Fun(
                fun.clone(),
                args.iter().map(|arg| self.apply(arg.as_ref())).collect(),
            ).into_arc(),
            RichFormula::Quantifier(q, arg) => {
                RichFormula::Quantifier(q.clone(), self.apply(arg.as_ref())).into_arc()
            }
        }
    }

    fn chain<O>(self: Self, other: O) -> Chain<Self, O>
    where
        Self: Sized,
        O: Substitution<'bump> + Sized,
    {
        Chain(self, other)
    }

    fn translate(self, i: usize) -> Chain<Self, Translate>
    where
        Self: Sized,
    {
        self.chain(Translate(i))
    }
}


pub struct Chain<A, B>(A, B);

impl<'bump, A: Substitution<'bump>, B: Substitution<'bump>> Substitution<'bump> for Chain<A, B> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        self.0.get(var).apply_substitution2(&self.1)
    }
}

pub struct Translate(usize);

impl Translate {
    pub fn new(i: usize) -> Self {
        Translate(i)
    }
}

impl<'bump> Substitution<'bump> for Translate {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        RichFormula::Var(Variable {
            id: var.id + self.0,
            ..var.clone()
        }).into_arc()
    }
}