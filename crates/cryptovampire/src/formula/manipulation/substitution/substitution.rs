use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::variable::{Variable, uvar};

/// To model substitutions, i.e., replacing varibales with some other formulas
pub trait Substitution<'bump> {
    /// get the substitued term associated to the [Variable] `var`.
    /// By convention, we expect the substitution to be defined on all [Variable], possibly becoming the identity function.
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump>;

    /// Recursively apply [Substitution::get] to substitute all the variables in `f`
    fn apply(&self, f: impl AsRef<RichFormula<'bump>>) -> ARichFormula<'bump> {
        match f.as_ref() {
            RichFormula::Var(v) => self.get(v),
            RichFormula::Fun(fun, args) => {
                RichFormula::Fun(*fun, args.iter().map(|arg| self.apply(arg)).collect()).into_arc()
            }
            RichFormula::Quantifier(q, arg) => {
                RichFormula::Quantifier(q.clone(), self.apply(arg)).into_arc()
            }
        }
    }

    /// To chain two substitutions.
    ///
    /// The resulting substitution apply the current `self` *then* `other`.
    ///
    /// See [Chain]
    fn chain<O>(self, other: O) -> Chain<Self, O>
    where
        Self: Sized,
        O: Substitution<'bump> + Sized,
    {
        Chain(self, other)
    }

    /// To translate the result by `i` (to ensure unicity of the variables)
    ///
    /// This is simply calling `self.chain(Translate(i))`.
    ///
    /// See [Translate]
    fn translate(self, i: uvar) -> Chain<Self, Translate>
    where
        Self: Sized,
    {
        self.chain(Translate(i))
    }
}

/// To chain two substitutions.
///
/// The resulting substitution apply the current `self` *then* `other`.
///
/// See [Substitution::chain], it is the only way to build such a substitution
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct Chain<A, B>(A, B);

impl<'bump, A: Substitution<'bump>, B: Substitution<'bump>> Substitution<'bump> for Chain<A, B> {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        self.0.get(var).apply_substitution2(&self.1)
    }
}

/// Translate the variables by a fixed `i`. (i.e., adds `i` to their [Variable::id])
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub struct Translate(uvar);

impl Translate {
    pub fn new(i: uvar) -> Self {
        Translate(i)
    }
}

impl<'bump> Substitution<'bump> for Translate {
    fn get(&self, var: &Variable<'bump>) -> ARichFormula<'bump> {
        RichFormula::Var(Variable {
            id: var.id + self.0,
            ..*var
        })
        .into_arc()
    }
}
