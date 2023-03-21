use std::fmt;
use std::ops::{Add, Deref};
use std::{collections::HashSet, fmt::Display};

use itertools::Itertools;

use crate::{problem::problem::Problem, smt::smt::SmtFormula, utils::utils::StackBox};

use super::{
    env::Environement,
    formula_iterator::{FormulaIterator, IteratorFlags},
    formula_user::FormulaUser,
    function::Function,
    quantifier::Quantifier,
    sort::Sort,
    unifier::{Substitution, Translate},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Vec<RichFormula<'bump>>),
    Quantifier(Quantifier, Vec<RichFormula<'bump>>),
}

#[derive(Debug, PartialOrd, Ord, Hash, Clone)]
pub struct Variable<'bump> {
    pub id: usize,
    pub sort: Sort<'bump>,
}

impl<'bump> fmt::Display for Variable<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "X{}", self.id)
    }
}

impl<'bump> PartialEq for Variable<'bump> {
    fn eq(&self, other: &Self) -> bool {
        if cfg!(debug_assertions) {
            if self.id == other.id {
                assert_eq!(self.sort, other.sort);
                true
            } else {
                false
            }
        } else {
            self.id == other.id
        }
    }
}

impl<'bump> Eq for Variable<'bump> {}

impl<'bump> RichFormula<'bump> {
    pub fn get_sort<'a>(&self, env: &Environement) -> Sort<'bump> {
        match self {
            RichFormula::Var(v) => v.sort.clone(),
            RichFormula::Fun(f, _) => f.get_output_sort(),
            RichFormula::Quantifier(q, _) => q.get_output_sort(env).clone(),
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
        fn aux<'a>(data: &mut HashSet<&'a Variable<'bump>>, f: &'a RichFormula<'bump>) {
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

    pub fn used_variables_iter<'a>(
        &'a self,
        pbl: &'a Problem,
    ) -> impl Iterator<Item = &'a Variable<'bump>> + 'a {
        FormulaIterator::new(
            StackBox::new(vec![self]),
            pbl,
            IteratorFlags::QUANTIFIER,
            |f, _| {
                let (o, r) = match f {
                    RichFormula::Var(v) => (Some(v), None),
                    RichFormula::Fun(_, args) => (None, Some(args.iter())),
                    _ => (None, None),
                };
                (o, r.into_iter().flatten())
            },
        )
    }

    pub fn used_variables_iter_with_pile<'a, 'b>(
        &'a self,
        pbl: &'a Problem,
        pile: &'b mut Vec<&'a RichFormula>,
    ) -> impl Iterator<Item = &'a Variable> + 'b {
        pile.clear();
        pile.push(self);

        FormulaIterator::new(pile, pbl, IteratorFlags::QUANTIFIER, |f, _| {
            let (o, r) = match f {
                RichFormula::Var(v) => (Some(v), None),
                RichFormula::Fun(_, args) => (None, Some(args.iter())),
                _ => (None, None),
            };
            (o, r.into_iter().flatten())
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = &RichFormula> {
        let mut pile = vec![self];
        std::iter::from_fn(move || {
            if let Some(f) = pile.pop() {
                match f {
                    RichFormula::Var(_) => {}
                    RichFormula::Fun(_, args) => pile.extend(args.iter()),
                    RichFormula::Quantifier(_, args) => pile.extend(args.iter()),
                }
                Some(f)
            } else {
                None
            }
        })
    }

    pub fn iter_with_quantifier<'a>(
        &'a self,
        pbl: &'a Problem,
    ) -> impl Iterator<Item = &'a RichFormula> {
        FormulaIterator::new(
            StackBox::new(vec![self]),
            pbl,
            IteratorFlags::QUANTIFIER,
            Self::default_f,
        )
    }

    fn default_f<'a>(
        f: &'a RichFormula,
        _: &'a Problem,
    ) -> (
        Option<&'a RichFormula>,
        impl Iterator<Item = &'a RichFormula>,
    ) {
        (
            Some(f),
            match f {
                RichFormula::Fun(_, args) => Some(args.iter()),
                _ => None,
            }
            .into_iter()
            .flatten(),
        )
    }

    pub fn custom_iter_w_quantifier<'a, 'b, F, T>(
        &'a self,
        pbl: &'a Problem,
        mut f: F,
    ) -> impl Iterator<Item = T> + 'b
    where
        F: FnMut(&'b RichFormula, &'b Problem) -> (Option<T>, Vec<&'b RichFormula>) + 'b,
        T: 'b,
        'a: 'b
    {
        FormulaIterator::new(
            StackBox::new(vec![self]),
            pbl,
            IteratorFlags::QUANTIFIER,
            move |a, b| {
                let (o, v) = f(a, b);
                (o, v.into_iter())
            },
        )
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
        F: Fn(&Variable) -> Self,
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
        F: Fn(&Variable) -> Option<Self>,
    {
        self.apply(|v| f(v).unwrap_or(Self::Var(v.clone())))
    }

    pub fn apply_substitution(self, vars: &[usize], fs: &[Self]) -> Self {
        debug_assert_eq!(vars.len(), fs.len());
        self.apply_some(|v| {
            vars.iter()
                .position(|v2| v2 == &v.id)
                .map(|i| fs[i].clone())
        })
    }

    pub fn apply_permutation2(&self, per: &impl Substitution) -> Self {
        per.apply(self)
    }

    pub fn translate_vars(&self, i: usize) -> Self {
        self.apply_permutation2(&Translate::new(i))
    }

    pub fn smt(&self) -> SmtFormula {
        self.into()
    }
}

impl<'bump> Variable<'bump> {
    pub fn new(id: usize, sort: Sort<'bump>) -> Self {
        Self { id, sort }
    }

    pub fn as_formula<T, U>(self, ctx: &T) -> U
    where
        T: FormulaUser<U>,
    {
        ctx.varf(self)
    }

    pub fn clone_to_formula<T, U>(&self, ctx: &T) -> U
    where
        T: FormulaUser<U>,
    {
        self.clone().as_formula(ctx)
    }

    pub fn sort(&self) -> &Sort<'bump> {
        &self.sort
    }

    pub fn id(&self) -> usize {
        self.id
    }
}

impl<'bump> Add<usize> for Variable<'bump> {
    type Output = Variable<'bump>;

    fn add(self, rhs: usize) -> Self::Output {
        Variable {
            id: self.id + rhs,
            ..self
        }
    }
}

pub fn sorts_to_variables<I: Deref<Target = Sort<'bump>>>(
    from: usize,
    s: impl Iterator<Item = I>,
) -> Vec<Variable> {
    s.enumerate()
        .map(|(i, s)| Variable::new(i + from, s.clone()))
        .collect()
}

impl<'bump> From<Variable<'bump>> for RichFormula<'bump> {
    fn from(v: Variable) -> Self {
        RichFormula::Var(v)
    }
}
impl<'bump> From<&Variable<'bump>> for RichFormula<'bump> {
    fn from(v: &Variable) -> Self {
        v.clone().into()
    }
}

impl<'bump> From<(usize, Sort<'bump>)> for Variable<'bump> {
    fn from(arg: (usize, Sort)) -> Self {
        let (id, sort) = arg;
        Variable { id, sort }
    }
}
impl<'bump> From<(Sort<'bump>, usize)> for Variable<'bump> {
    fn from(arg: (Sort, usize)) -> Self {
        let (sort, id) = arg;
        Variable { id, sort }
    }
}

impl<'bump, 'a:'bump> From<(usize, &'a Sort<'bump>)> for Variable<'bump> {
    fn from(arg: (usize, &'a Sort)) -> Self {
        let (id, sort) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}
impl<'bump, 'a:'bump> From<(&'a Sort<'bump>, usize)> for Variable<'bump> {
    fn from(arg: (&'a Sort, usize)) -> Self {
        let (sort, id) = arg;
        Variable {
            id,
            sort: sort.clone(),
        }
    }
}

impl<'bump> Display for RichFormula<'bump> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        SmtFormula::from(self).fmt(f)
    }
}

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
