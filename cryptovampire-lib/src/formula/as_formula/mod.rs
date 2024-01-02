//! lazy map

use super::{formula::RichFormula, function::Function, quantifier::Quantifier, variable::Variable};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum FormulaLike<T, I, F, V, Q>
where
    I: IntoIterator<Item = T>,
{
    Var(V),
    Fun(F, I),
    Quantifier(Q, Box<T>),
}

type RichFormulaLike<'bump, T, I = Vec<T>> =
    FormulaLike<T, I, Function<'bump>, Variable<'bump>, Quantifier<'bump>>;

pub trait FormulaLikeT<'bump>: Sized {
    type Iter: IntoIterator<Item = Self>;
    type Var: Into<Variable<'bump>>;
    type Fun: Into<Function<'bump>>;
    type Quant: Into<Quantifier<'bump>>;

    fn next(self) -> RichFormulaLike<'bump, Self, Self::Iter>;
    fn apply(self) -> RichFormula<'bump> {
        match self.next() {
            FormulaLike::Var(v) => RichFormula::Var(v.into()),
            FormulaLike::Fun(f, args) => {
                RichFormula::Fun(f.into(), args.into_iter().map(Self::apply).collect())
            }
            FormulaLike::Quantifier(q, arg) => {
                RichFormula::Quantifier(q.into(), Box::new(arg.apply()))
            }
        }
    }
}

impl<'bump> FormulaLikeT<'bump> for RichFormula<'bump> {
    type Iter = Vec<Self>;
    type Var = Variable<'bump>;
    type Fun = Function<'bump>;
    type Quant = Quantifier<'bump>;

    fn next(self) -> RichFormulaLike<'bump, Self, Self::Iter> {
        match self {
            RichFormula::Var(v) => RichFormulaLike::Var(v),
            RichFormula::Fun(fun, args) => RichFormulaLike::Fun(fun, args),
            RichFormula::Quantifier(q, arg) => RichFormulaLike::Quantifier(q, arg),
        }
    }

    fn apply(self) -> RichFormula<'bump> {
        self
    }
}
