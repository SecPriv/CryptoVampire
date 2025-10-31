use log::trace;
use utils::arc_into_iter::ArcIntoIter;

use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::manipulation::Unifier;
use crate::formula::sort::Sort;
use crate::formula::variable::Variable;

// use self::possibly_empty::PE;

#[derive(Debug, Clone)]
pub struct SubtermResult<'bump, I> {
    pub unifier: Option<Unifier<'bump>>,
    pub nexts: I,
}

#[derive(Debug, Clone)]
pub struct VarSubtermResult<'bump, I>
where
    I: IntoIterator<Item = ARichFormula<'bump>>,
{
    pub unified: bool,
    pub nexts: I,
}

pub trait SubtermAux<'bump> {
    type IntoIter: IntoIterator<Item = ARichFormula<'bump>>;

    fn is_subterm_and_next(
        &self,
        x: &ARichFormula<'bump>,
        m: &ARichFormula<'bump>,
    ) -> SubtermResult<'bump, Self::IntoIter> {
        let VarSubtermResult {
            unified: unifier,
            nexts,
        } = self.var_eval_and_next(m);
        if unifier {
            match x.as_ref() {
                RichFormula::Var(v) => SubtermResult {
                    unifier: Some(Unifier::one_variable_unifier(v, m.shallow_copy())),
                    nexts,
                },
                _ => {
                    let mgu = Unifier::mgu(x, m);
                    if cfg!(debug_assertions) && mgu.is_some() {
                        trace!("match!:\n{x}\n{m}")
                    }

                    SubtermResult {
                        unifier: mgu,
                        nexts,
                    }
                }
            }
        } else {
            SubtermResult {
                unifier: None,
                nexts,
            }
        }
    }

    /// `eval_and_next` but optimized for variable only
    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let x = Variable {
            id: 0,
            sort: self.sort(),
        }
        .into_aformula();
        let SubtermResult { unifier, nexts } = self.is_subterm_and_next(&x, m);
        VarSubtermResult {
            unified: unifier.is_some(),
            nexts,
        }
    }

    fn eval(&self, x: &ARichFormula<'bump>, m: &ARichFormula<'bump>) -> bool {
        self.is_subterm_and_next(x, m).unifier.is_some()
    }

    fn nexts(&self, x: &ARichFormula<'bump>, m: &ARichFormula<'bump>) -> Self::IntoIter {
        self.is_subterm_and_next(x, m).nexts
    }

    fn sort(&self) -> Sort<'bump>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DefaultAuxSubterm<'bump> {
    pub sort: Sort<'bump>,
}

impl<'bump> DefaultAuxSubterm<'bump> {
    pub fn new(sort: Sort<'bump>) -> Self {
        DefaultAuxSubterm { sort }
    }
}

impl<'bump> SubtermAux<'bump> for DefaultAuxSubterm<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let nexts = match m.as_ref() {
            RichFormula::Fun(_, args) => args.into(),
            RichFormula::Quantifier(_, arg) => [arg.shallow_copy()].into(),
            _ => [].into(),
        };

        let x_sort = self.sort();
        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.map(|m_sort| x_sort == m_sort).unwrap_or(true), /* m_sort.is_err() || x_sort == m_sort.unwrap(), */
            nexts,
        }
    }

    fn sort(&self) -> Sort<'bump> {
        self.sort
    }
}
