use std::sync::Arc;

use itertools::{Either, chain, izip};
use logic_formula::{AsFormula, Bounder, Destructed, HeadSk};

use super::ARichFormula;
use crate::formula::function::Function;
use crate::formula::function::inner::term_algebra;
use crate::formula::quantifier::Quantifier;
use crate::formula::variable::Variable;

/// A wapper around [ARichFormula] to iterate through ta quantifiers
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct Expander<'a, 'bump> {
    /// The formula to iterate through
    formula: &'a ARichFormula<'bump>,
    /// a substitution, see [Self::destruct]'s source to see how it is used
    substitution: Arc<[(Variable<'bump>, &'a ARichFormula<'bump>)]>,
}

impl<'a, 'bump> Expander<'a, 'bump> {
    pub fn formula(&self) -> &ARichFormula<'bump> {
        self.formula
    }
}

impl<'a, 'bump> AsFormula for Expander<'a, 'bump> {
    type Var = Variable<'bump>;

    type Fun = Function<'bump>;

    type Quant = EitherQuantifier<'bump>;

    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        let Self {
            formula,
            substitution,
        } = self;
        let Destructed { head, args } = formula.destruct();
        match head {
            // if it's a regular quantifier, cast to the new type and continue normally
            HeadSk::Quant(q) => Destructed {
                head: HeadSk::Quant(q.into()),
                args: Either::Left(commun_f(substitution, args)),
            },
            // if it's a variable
            HeadSk::Var(v) => {
                // if it's in the substitution
                if let Some(formula) = substitution
                    .iter()
                    .rev()
                    .find_map(|(sv, f)| (sv == &v).then_some(*f))
                {
                    // apply the substitution and try again
                    Self {
                        substitution,
                        formula,
                    }
                    .destruct()
                } else {
                    // otherwise to the thing regularily
                    Destructed {
                        head: HeadSk::Var(v),
                        args: Either::Left(commun_f(substitution, args)),
                    }
                }
            }
            // if it's a function
            HeadSk::Fun(f) => match f.as_quantifer() {
                // if it'ss a regular function, do the usual
                None => Destructed {
                    head: HeadSk::Fun(f),
                    args: Either::Left(commun_f(substitution, args)),
                },
                // if it's a ta quantifier
                Some(q) => {
                    // update the substitution
                    // note that we need to copy the whole content of the old `substitution`
                    // so using something like an Arc<[ ]> doesn't make us lose performance
                    // over a Vec-like structure. (plus the sized should be known before hand)
                    let substitution: Arc<[_]> = chain!(
                        substitution.iter().map(|(a, b)| (*a, *b)),
                        izip!(q.free_variables.iter().cloned(), q.get_content_iter())
                    )
                    .collect();
                    // return the new object with the new substitution
                    Destructed {
                        head: HeadSk::Quant(q.into()),
                        args: Either::Right(args.map(move |formula| Self {
                            formula,
                            substitution: substitution.clone(),
                        })),
                    }
                }
            },
        }
    }
}

fn commun_f<'a, 'bump>(
    substitutions: Arc<[(Variable<'bump>, &'a ARichFormula<'bump>)]>,
    args: impl Iterator<Item = &'a ARichFormula<'bump>>,
) -> impl Iterator<Item = Expander<'a, 'bump>> {
    args.map(move |formula| Expander {
        formula,
        substitution: Arc::clone(&substitutions),
    })
}

impl<'a, 'bump> From<&'a ARichFormula<'bump>> for Expander<'a, 'bump> {
    fn from(formula: &'a ARichFormula<'bump>) -> Self {
        Self {
            formula,
            substitution: Arc::new([]),
        }
    }
}

/// Gather regular quantifiers and ta quantifiers
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub enum EitherQuantifier<'bump> {
    Bool(Quantifier<'bump>),
    TermAlgebra(&'bump term_algebra::quantifier::Quantifier<'bump>),
}

impl<'bump> From<&'bump term_algebra::quantifier::Quantifier<'bump>> for EitherQuantifier<'bump> {
    fn from(v: &'bump term_algebra::quantifier::Quantifier<'bump>) -> Self {
        Self::TermAlgebra(v)
    }
}

impl<'bump> From<Quantifier<'bump>> for EitherQuantifier<'bump> {
    fn from(v: Quantifier<'bump>) -> Self {
        Self::Bool(v)
    }
}
impl<'bump> Bounder<Variable<'bump>> for EitherQuantifier<'bump> {
    fn bounds(&self) -> impl Iterator<Item = Variable<'bump>> {
        match self {
            EitherQuantifier::Bool(q) => q.get_variables().iter(),
            EitherQuantifier::TermAlgebra(q) => q.bound_variables.iter(),
        }
        .cloned()
    }
}
