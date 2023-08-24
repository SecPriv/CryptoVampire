use crate::{
    formula::{
        formula::{ARichFormula, RichFormula},
        manipulation::Unifier,
        sort::Sort,
        variable::Variable,
    },
    utils::arc_into_iter::ArcIntoIter,
};

// use self::possibly_empty::PE;

#[derive(Debug, Clone)]
pub struct SubtermResult<'bump, I>
where
    I: IntoIterator<Item = ARichFormula<'bump>>,
{
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

    fn eval_and_next(
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
                // _ => {
                //     if let Some(unifier) = Unifier::mgu(x, m) {
                //         SubtermResult {
                //             unifier: Some(unifier),
                //             nexts,
                //         }
                //     } else {
                //         unreachable!("Inconsistent mgu result with `var_eval_and_next`");
                //     }
                // }
                _ => {
                    let mgu = Unifier::mgu(x, m);
                    if cfg!(debug_assertions) && mgu.is_some() {
                        println!("\t\t\tmatch!");
                    }

                    SubtermResult {
                    unifier: mgu,
                    nexts,
                }},
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
        let SubtermResult { unifier, nexts } = self.eval_and_next(&x, m);
        VarSubtermResult {
            unified: unifier.is_some(),
            nexts,
        }
    }

    fn eval(&self, x: &ARichFormula<'bump>, m: &ARichFormula<'bump>) -> bool {
        self.eval_and_next(x, m).unifier.is_some()
    }

    fn nexts(&self, x: &ARichFormula<'bump>, m: &ARichFormula<'bump>) -> Self::IntoIter {
        self.eval_and_next(x, m).nexts
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

static EMPTY_SLICE: [RichFormula<'static>; 0] = [];

impl<'bump> SubtermAux<'bump> for DefaultAuxSubterm<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    // fn eval_and_next<'a>(
    //     &self,
    //     x: ARichFormula<'bump>,
    //     m: ARichFormula<'bump>,
    // ) -> SubtermResult<'a, 'bump, Self::IntoIter<'a>>
    // where
    //     'bump: 'a,
    // {
    //     let unifier = Unifier::mgu(x, m);
    //     let nexts = match m {
    //         RichFormula::Fun(_, args) => PE::new(args.as_slice()), //args.as_slice(),
    //         _ => PE::empty(),
    //     };

    //     SubtermResult { unifier, nexts }
    // }

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
            unified: m_sort.map(|m_sort| x_sort == m_sort).unwrap_or(true), // m_sort.is_err() || x_sort == m_sort.unwrap(),
            nexts,
        }
    }

    fn sort(&self) -> Sort<'bump> {
        self.sort
    }
}

// mod possibly_empty {
// }
