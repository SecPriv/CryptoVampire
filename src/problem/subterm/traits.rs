use crate::formula::{formula::RichFormula, unifier::Unifier};

use self::possibly_empty::PE;

#[derive(Debug, Clone)]
pub struct SubtermResult<'a, 'bump, I>
where
    I: IntoIterator<Item = &'a RichFormula<'bump>>,
    'bump: 'a,
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
    fn eval_and_next<'a>(
        &self,
        x: &'a RichFormula<'bump>,
        m: &'a RichFormula<'bump>,
    ) -> SubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let VarSubtermResult {
            unified: unifier,
            nexts,
        } = self.var_eval_and_next(x, m);
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
        x: &'a RichFormula<'bump>,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let SubtermResult { unifier, nexts } = self.eval_and_next(x, m);
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
}

pub struct DefaultAuxSubterm();

static EMPTY_SLICE: [RichFormula<'static>; 0] = [];

impl<'bump> SubtermAux<'bump> for DefaultAuxSubterm {
    type IntoIter<'a> = PE<'a, 'bump>
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
        x: &'a RichFormula<'bump>,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let nexts = match m {
            RichFormula::Fun(_, args) => PE::new(args.as_slice()), //args.as_slice(),
            _ => PE::empty(),
        };

        let x_sort = x.get_sort();
        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: x_sort.is_err() || m_sort.is_err() || x_sort.unwrap() == m_sort.unwrap(),
            nexts,
        }
    }
}

mod possibly_empty {
    use crate::formula::formula::RichFormula;

    pub enum PE<'a, 'bump> {
        Empty,
        NotEmpty {
            vec: &'a [RichFormula<'bump>],
            i: usize,
        },
    }

    impl<'a, 'bump> PE<'a, 'bump> {
        pub fn new(vec: &'a [RichFormula<'bump>]) -> Self {
            Self::NotEmpty { vec, i: 0 }
        }

        pub fn empty() -> Self {
            Self::Empty
        }
    }

    impl<'a, 'bump> Iterator for PE<'a, 'bump> {
        type Item = &'a RichFormula<'bump>;

        fn next(&mut self) -> Option<Self::Item> {
            match self {
                PE::Empty => None,
                PE::NotEmpty { vec, i } => vec.get(*i).map(|x| {
                    *i += 1;
                    x
                }),
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            match self {
                PE::Empty => (0, Some(0)),
                PE::NotEmpty { vec, i } => vec[*i..].iter().size_hint(),
            }
        }
    }

    impl<'a, 'bump> ExactSizeIterator for PE<'a, 'bump> {
        fn len(&self) -> usize {
            let (lower, upper) = self.size_hint();
            assert_eq!(upper, Some(lower));
            lower
        }

    }
}
