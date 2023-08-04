use crate::formula::{variable::Variable, formula::RichFormula};


pub trait Substitution<'bump> {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump>;

    fn apply(&self, f: &RichFormula<'bump>) -> RichFormula<'bump> {
        match f {
            RichFormula::Var(v) => self.get(v),
            RichFormula::Fun(fun, args) => RichFormula::Fun(
                fun.clone(),
                args.iter().map(|arg| self.apply(arg)).collect(),
            ),
            RichFormula::Quantifier(q, arg) => {
                RichFormula::Quantifier(q.clone(), Box::new(self.apply(arg.as_ref())))
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
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        self.0.get(var).apply_permutation2(&self.1)
    }
}

pub struct Translate(usize);

impl Translate {
    pub fn new(i: usize) -> Self {
        Translate(i)
    }
}

impl<'bump> Substitution<'bump> for Translate {
    fn get(&self, var: &Variable<'bump>) -> RichFormula<'bump> {
        RichFormula::Var(Variable {
            id: var.id + self.0,
            ..var.clone()
        })
    }
}