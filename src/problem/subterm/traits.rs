use crate::{
    formula::{formula::RichFormula, sort::Sort, unifier::Unifier, variable::Variable},
    utils::vecref::VecRef,
};

// use self::possibly_empty::PE;

#[derive(Debug, Clone)]
pub struct SubtermResult<'a, 'b, 'bump, I>
where
    I: IntoIterator<Item = &'b RichFormula<'bump>>,
    'bump: 'b,
    'b: 'a,
{
    pub unifier: Option<Unifier<'a, 'bump>>,
    pub nexts: I,
}

#[derive(Debug, Clone)]
pub struct VarSubtermResult<'a, 'bump, I>
where
    I: IntoIterator<Item = &'a RichFormula<'bump>>,
    'bump: 'a,
{
    pub unified: bool,
    pub nexts: I,
}

pub trait SubtermAux<'bump> {
    type IntoIter<'a>: IntoIterator<Item = &'a RichFormula<'bump>> + 'a
    where
        'bump: 'a;
    fn eval_and_next<'a, 'b>(
        &self,
        x: &'a RichFormula<'bump>,
        m: &'b RichFormula<'bump>,
    ) -> SubtermResult<'a, 'b, 'bump, Self::IntoIter<'b>>
    where
        'bump: 'b,
        'b: 'a,
    {
        let VarSubtermResult {
            unified: unifier,
            nexts,
        } = self.var_eval_and_next(m);
        if unifier {
            match x {
                RichFormula::Var(v) => SubtermResult {
                    unifier: Some(Unifier::one_variable_unifier(v, m)),
                    nexts,
                },
                _ => {
                    if let Some(unifier) = Unifier::mgu(x, m) {
                        SubtermResult {
                            unifier: Some(unifier),
                            nexts,
                        }
                    } else {
                        unreachable!("Inconsistent mgu result with `var_eval_and_next`");
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
    fn var_eval_and_next<'a>(
        &self,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let x = Variable {
            id: 0,
            sort: self.sort(),
        }
        .into_formula();
        let SubtermResult { unifier, nexts } = self.eval_and_next(&x, m);
        VarSubtermResult {
            unified: unifier.is_some(),
            nexts,
        }
    }

    fn eval<'a>(&self, x: &'a RichFormula<'bump>, m: &'a RichFormula<'bump>) -> bool
    where
        'bump: 'a,
    {
        self.eval_and_next(x, m).unifier.is_some()
    }

    fn nexts<'a>(&self, x: &'a RichFormula<'bump>, m: &'a RichFormula<'bump>) -> Self::IntoIter<'a>
    where
        'bump: 'a,
    {
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
    type IntoIter<'a> = VecRef<'a, RichFormula<'bump>>
    where
        'bump: 'a;

    // fn eval_and_next<'a>(
    //     &self,
    //     x: &'a RichFormula<'bump>,
    //     m: &'a RichFormula<'bump>,
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

    fn var_eval_and_next<'a>(
        &self,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let nexts = match m {
            RichFormula::Fun(_, args) => VecRef::Ref(args),
            _ => VecRef::Empty,
        };

        let x_sort = self.sort();
        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.is_err() || x_sort == m_sort.unwrap(),
            nexts,
        }
    }

    fn sort(&self) -> Sort<'bump> {
        self.sort
    }
}

// mod possibly_empty {
// }
