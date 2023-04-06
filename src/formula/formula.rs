use std::collections::HashSet;
use std::ops::{BitAnd, BitOr, Deref, DerefMut, Not, Shr};

use itertools::Itertools;

use crate::problem::protocol::Protocol;
use crate::utils::utils::{repeat_n_zip, StackBox};

use super::function::builtin::{AND, EQUALITY, IMPLIES, NOT, OR};
use super::sort::builtins::BOOL;
use super::sort::sorted::{Sorted, SortedError};
use super::utils::formula_expander::{self, ExpantionContent, ExpantionState};
use super::utils::formula_iterator::{FormulaIterator, IteratorFlags};
use super::variable::Variable;
use super::{
    function::Function,
    quantifier::Quantifier,
    sort::Sort,
    unifier::{Substitution, Translate},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Vec<RichFormula<'bump>>),
    Quantifier(Quantifier<'bump>, Vec<RichFormula<'bump>>),
}

impl<'bump> RichFormula<'bump> {
    pub fn get_sort(&self) -> Result<Sort<'bump>, SortedError> {
        match self {
            RichFormula::Var(Variable { sort, .. }) => Ok(*sort),
            RichFormula::Fun(fun, args) => {
                let args: Result<Vec<_>, _> = args.iter().map(|arg| arg.get_sort()).collect();
                fun.sort(args?.as_slice())
            }
            RichFormula::Quantifier(_q, _) => Ok(BOOL.as_sort()),
        }
    }

    pub fn get_free_vars(&self) -> Vec<&Variable<'bump>> {
        let mut free_vars = Vec::new();
        let mut bound_vars = Vec::new();

        for f in self.iter() {
            match f {
                RichFormula::Var(v) if !(free_vars.contains(&v) || bound_vars.contains(&v)) => {
                    free_vars.push(v)
                }
                RichFormula::Quantifier(q, _) => {
                    for v in q.get_variables() {
                        debug_assert!(
                            !free_vars.contains(&v),
                            "\n\tfv:{:?}\n\t{:?}",
                            &free_vars,
                            &v
                        );
                        if !bound_vars.contains(&v) {
                            bound_vars.push(v)
                        }
                    }
                }
                _ => {}
            }
        }
        free_vars
    }

    /// doesn't go though all quantifiers
    pub fn get_used_variables(&'_ self) -> HashSet<&'_ Variable<'bump>> {
        fn aux<'a, 'bump>(data: &mut HashSet<&'a Variable<'bump>>, f: &'a RichFormula<'bump>) {
            match f {
                RichFormula::Var(v) => {
                    data.insert(v);
                }
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(data, f)),
                RichFormula::Quantifier(q, args) => {
                    data.extend(q.get_variables().iter().map(|v| v));
                    args.iter().for_each(|f| aux(data, f))
                }
            }
        }

        let mut data = HashSet::new();
        aux(&mut data, self);
        data
    }

    pub fn used_variables_iter<'a: 'bump>(
        &'a self,
    ) -> impl Iterator<Item = &'a Variable<'bump>> + 'a {
        self.used_variables_iter_with_pile(StackBox::new(Vec::with_capacity(1)))
    }

    pub fn used_variables_iter_with_pile<'a, V>(
        &'a self,
        pile: V,
    ) -> impl Iterator<Item = &'a Variable<'bump>>
    where
        V: DerefMut<Target = Vec<((), &'a RichFormula<'bump>)>>
            + Deref<Target = Vec<((), &'a RichFormula<'bump>)>>,
    {
        self.iter_with_pile(pile).filter_map(|f| match f {
            RichFormula::Var(v) => Some(v),
            _ => None,
        })
    }

    pub fn iter_with_pile<'a, V>(
        &'a self,
        mut pile: V,
    ) -> impl Iterator<Item = &'a RichFormula<'bump>>
    where
        V: DerefMut<Target = Vec<((), &'a Self)>> + Deref<Target = Vec<((), &'a Self)>>,
    {
        pile.clear();
        pile.push(((), self));
        FormulaIterator {
            pile,
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let next = match f {
                    RichFormula::Fun(_, args) => Some(args.iter()),
                    _ => None,
                };
                (Some(f), repeat_n_zip((), next.into_iter().flatten()))
            },
        }
    }

    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a RichFormula<'bump>> {
        self.iter_with_pile(StackBox::new(vec![]))
    }

    pub fn map<F>(self, f: &F) -> Self
    where
        F: Fn(Self) -> Self,
    {
        match self {
            RichFormula::Var(_) => f(self),
            RichFormula::Fun(fun, args) => {
                f(Self::Fun(fun, args.into_iter().map(|x| x.map(f)).collect()))
            }
            RichFormula::Quantifier(q, args) => f(Self::Quantifier(
                q,
                args.into_iter().map(|x| x.map(f)).collect(),
            )),
        }
    }

    pub fn apply<F>(self, f: F) -> Self
    where
        F: Fn(&Variable<'bump>) -> Self,
    {
        self.map(&{
            |form| match form {
                Self::Var(v) => f(&v),
                _ => form,
            }
        })
    }

    pub fn apply_some<F>(self, f: F) -> Self
    where
        F: Fn(&Variable<'bump>) -> Option<Self>,
    {
        self.apply(|v: &Variable| f(v).unwrap_or(Self::Var(v.clone())))
    }

    pub fn apply_substitution(self, vars: &[usize], fs: &[Self]) -> Self {
        debug_assert_eq!(vars.len(), fs.len());
        self.apply_some(|v| {
            vars.iter()
                .position(|v2| v2 == &v.id)
                .map(|i| fs[i].clone())
        })
    }

    pub fn apply_permutation2(&self, per: &impl Substitution<'bump>) -> Self {
        per.apply(self)
    }

    pub fn translate_vars(&self, i: usize) -> Self {
        self.apply_permutation2(&Translate::new(i))
    }

    // pub fn smt(&self) -> SmtFormula {
    //     self.into()
    // }

    pub fn ands(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
        AND.f(args)
    }

    pub fn ors(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
        OR.f(args)
    }

    pub fn expand<'a>(
        &'a self,
        ptcl: &Protocol<'bump>,
        with_args: bool,
    ) -> Vec<ExpantionContent<'a, 'bump>> {
        ExpantionContent {
            state: ExpantionState::None,
            content: &self,
        }
        .expand(ptcl.steps.iter().cloned(), &ptcl.graph, with_args)
    }
}

impl<'bump> From<Variable<'bump>> for RichFormula<'bump> {
    fn from(v: Variable<'bump>) -> Self {
        RichFormula::Var(v)
    }
}
impl<'bump> From<&Variable<'bump>> for RichFormula<'bump> {
    fn from(v: &Variable<'bump>) -> Self {
        v.clone().into()
    }
}

// impl<'bump> Display for RichFormula<'bump> {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         SmtFormula::from(self).fmt(f)
//     }
// }

// pub fn get_eval_msg(env:&Environement) -> impl Fn(RichFormula) -> RichFormula {
//     let eval = env.get_f(EVAL_MSG_NAME).unwrap().clone();
//     let no_ta = env.no_ta();
//     move |f| {
//         if !no_ta {
//             RichFormula::Fun(eval.clone(), vec![f])
//         } else {
//             f
//         }
//     }
// }

// pub fn get_eval_cond(env:&Environement) -> impl Fn(RichFormula) -> RichFormula {
//     let eval = env.get_f(EVAL_COND_NAME).unwrap().clone();
//     // let ctrue = env.get_f(CTRUE_NAME).unwrap().clone();
//     let no_ta = env.no_ta();
//     move |f| {
//         if !no_ta {
//             RichFormula::Fun(eval.clone(), vec![f])
//         } else {
//             RichFormula::Fun(eval.clone(), vec![f])
//         }
//     }
// }

impl<'bump> BitAnd for RichFormula<'bump> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        AND.f([self, rhs])
    }
}

impl<'bump> BitOr for RichFormula<'bump> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        OR.f([self, rhs])
    }
}

impl<'bump> Not for RichFormula<'bump> {
    type Output = Self;

    fn not(self) -> Self::Output {
        NOT.f([self])
    }
}

impl<'bump> Shr for RichFormula<'bump> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        IMPLIES.f([self, rhs])
    }
}

fn enlarge<'a, 'b>(q: RichFormula<'a>) -> RichFormula<'b>
where
    'a: 'b,
{
    q
}

pub fn forall<'bump>(
    vars: impl IntoIterator<Item = Variable<'bump>>,
    arg: RichFormula<'bump>,
) -> RichFormula<'bump> {
    RichFormula::Quantifier(
        Quantifier::Forall {
            variables: vars.into_iter().collect(),
        },
        vec![arg],
    )
}

pub fn exists<'bump>(
    vars: impl IntoIterator<Item = Variable<'bump>>,
    arg: RichFormula<'bump>,
) -> RichFormula<'bump> {
    RichFormula::Quantifier(
        Quantifier::Exists {
            variables: vars.into_iter().collect(),
        },
        vec![arg],
    )
}

pub fn meq<'bump>(lhs: RichFormula<'bump>, rhs: RichFormula<'bump>) -> RichFormula<'bump> {
    EQUALITY.f([lhs, rhs])
}
