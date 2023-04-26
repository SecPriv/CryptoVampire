use std::collections::HashSet;
use std::env::var;
use std::ops::{BitAnd, BitOr, Deref, DerefMut, Not, Shr};

use itertools::Itertools;

use crate::problem::protocol::Protocol;
use crate::utils::utils::{repeat_n_zip, StackBox};

use super::function::builtin::{AND, EQUALITY, IMPLIES, NOT, OR};
use super::sort::builtins::BOOL;
use super::sort::sorted::{Sorted, SortedError};
use super::utils::formula_expander::{self, DeeperKinds, ExpantionContent, ExpantionState};
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
    Quantifier(Quantifier<'bump>, Box<RichFormula<'bump>>),
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

    pub fn iter_used_varibales_with_pile<'a, V, D>(
        mut pile: V,
        fs: impl IntoIterator<Item = &'a RichFormula<'bump>>,
    ) -> impl Iterator<Item = Variable<'bump>> + 'a
    where
        V: DerefMut<Target = Vec<(D, &'a Self)>> + Deref<Target = Vec<(D, &'a Self)>> + 'a,
        D: Default + Clone + 'a,
        'bump: 'a,
    {
        pile.clear();
        pile.extend(fs.into_iter().map(|f| (Default::default(), f)));
        FormulaIterator {
            pile,
            passed_along: None,
            flags: IteratorFlags::QUANTIFIER,
            f: |_, f| {
                let (current, next) = match f {
                    RichFormula::Var(v) => (Some(*v), None),
                    RichFormula::Fun(_, args) => (None, Some(args.iter())),
                    _ => (None, None),
                };
                (
                    current,
                    next.into_iter().flatten().map(|f| (Default::default(), f)),
                )
            },
        }
    }

    pub fn iter_used_varibales<'a>(
        fs: impl IntoIterator<Item = &'a RichFormula<'bump>>,
    ) -> impl Iterator<Item = Variable<'bump>> + 'a
    where
        'bump: 'a,
    {
        Self::iter_used_varibales_with_pile(StackBox::new(Vec::<((), _)>::new()), fs)
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
                // args.into_iter().map(|x| x.map(f)).collect(),
                Box::new(args.map(f))
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
        deeper_kind: DeeperKinds,
    ) -> Vec<ExpantionContent<'a, 'bump>> {
        ExpantionContent {
            state: ExpantionState::None,
            content: &self,
        }
        .expand(
            ptcl.steps.iter().cloned(),
            &ptcl.graph,
            with_args,
            deeper_kind,
        )
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

fn _enlarge<'a, 'b>(q: RichFormula<'a>) -> RichFormula<'b>
where
    'a: 'b,
{
    q
}

pub fn forall<'bump>(
    vars: impl IntoIterator<Item = Variable<'bump>>,
    arg: RichFormula<'bump>,
) -> RichFormula<'bump> {
    let mut vars = vars.into_iter().peekable();
    if let Some(_) = vars.peek() {
        let variables = vars.collect_vec();
        RichFormula::Quantifier(Quantifier::Forall { variables }, Box::new(arg))
    } else {
        arg
    }
}

pub fn exists<'bump>(
    vars: impl IntoIterator<Item = Variable<'bump>>,
    arg: RichFormula<'bump>,
) -> RichFormula<'bump> {
    let mut vars = vars.into_iter().peekable();
    if let Some(_) = vars.peek() {
        let variables = vars.collect_vec();
        RichFormula::Quantifier(Quantifier::Exists { variables }, Box::new(arg))
    } else {
        arg
    }
}

pub fn meq<'bump>(lhs: RichFormula<'bump>, rhs: RichFormula<'bump>) -> RichFormula<'bump> {
    EQUALITY.f([lhs, rhs])
}

pub mod macros {
    #[macro_export]
    macro_rules! mforall {
        ($($var:ident!$n:literal:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::formula::variable::Variable { id: $n, sort: $sort};
            )*
            $crate::formula::formula::forall([$($var),*], {
                $(
                    let $var = $var.into_formula();
                )*
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::formula::formula::forall($vars, $content)
        }
    }

    #[macro_export]
    macro_rules! mexists {
        ($($var:ident!$n:literal:$sort:expr),*; $content:block) => {{
            $(
                let $var = $crate::formula::variable::Variable { id: $n, sort: $sort};
            )*
            $crate::formula::formula::exists([$($var),*], {
                $(
                    let $var = $var.into_formula();
                )*
                $content
            })
        }};
        ($vars:expr, $content:block) => {
            $crate::formula::formula::exists($vars, $content)
        }
    }

    pub use {mexists, mforall};
}
