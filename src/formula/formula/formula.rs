use std::{
    fmt::Display,
    ops::{BitAnd, BitOr, Not, Shr},
    sync::Arc,
};

use hashbrown::HashSet;
use itertools::Itertools;

use crate::{
    formula::{
        formula::ARichFormula,
        function::{
            builtin::{AND, EQUALITY, IMPLIES, NOT, OR},
            signature::Signature,
            Function,
        },
        manipulation::{Substitution, Translate},
        quantifier::Quantifier,
        sort::{
            builtins::BOOL,
            sorted::{Sorted, SortedError},
            Sort,
        },
        utils::formula_expander::{DeeperKinds, ExpantionContent, ExpantionState},
        variable::Variable,
    },
    implvec,
    problem::protocol::Protocol,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Arc<[ARichFormula<'bump>]>), //Vec<RichFormula<'bump>>),
    Quantifier(Quantifier<'bump>, ARichFormula<'bump>),
}

impl<'bump> RichFormula<'bump> {
    pub fn get_sort(&self) -> Result<Sort<'bump>, SortedError> {
        println!("  checksort -> {self}");
        match self {
            RichFormula::Var(Variable { sort, .. }) => Ok(*sort),
            RichFormula::Fun(fun, args) => {
                let args: Result<Vec<_>, _> = args.iter().map(|arg| arg.get_sort()).collect();
                fun.sort(args?.as_slice())
            }
            RichFormula::Quantifier(_q, _) => Ok(BOOL.as_sort()),
        }
    }

    pub fn sort(&self) -> Option<Sort<'bump>> {
        match self {
            RichFormula::Var(v) => Some(v.sort),
            RichFormula::Fun(fun, _) => fun.signature().out().into(),
            RichFormula::Quantifier(_, _) => Some(BOOL.as_sort()),
        }
    }
    pub fn get_free_vars(&'_ self) -> Vec<Variable<'bump>> {
        let mut free_vars = Vec::new();
        let mut todo = vec![self];
        Self::get_free_vars_with_pile(&mut todo, &mut free_vars);
        free_vars
    }

    pub fn get_free_vars_with_pile<'a>(
        todo: &mut Vec<&'a RichFormula<'bump>>,
        free_vars: &mut Vec<Variable<'bump>>,
    ) where
        'bump: 'a,
    {
        let mut bound_vars = Vec::new();
        let mut var_stack = vec![(todo.len(), 0)];

        fn decr<'a, 'bump: 'a>(
            var_stack: &mut Vec<(usize, usize)>,
            bound_vars: &mut Vec<Variable<'bump>>,
        ) {
            let (depth, vars) = var_stack.last_mut().unwrap();
            *depth -= 1;
            if *depth == 0 {
                bound_vars.truncate(bound_vars.len() - *vars);
                var_stack.pop();
            }
        }

        fn incr<'a, 'bump: 'a>(
            var_stack: &mut Vec<(usize, usize)>,
            bound_vars: &mut Vec<Variable<'bump>>,
            todo: &mut Vec<&'a RichFormula<'bump>>,
            args: &'a [ARichFormula<'bump>],
        ) {
            todo.extend(args.iter().map(|af| af.as_ref()));
            var_stack.last_mut().unwrap().0 += args.len();
            decr(var_stack, bound_vars)
        }

        fn add_vars<'a, 'bump: 'a>(
            bound_vars: &mut Vec<Variable<'bump>>,
            var_stack: &mut Vec<(usize, usize)>,
            vars: &'a [Variable<'bump>],
        ) {
            bound_vars.extend(vars.iter());
            var_stack.push((1, vars.len()));
        }

        while let Some(t) = todo.pop() {
            match t {
                RichFormula::Var(v) => {
                    if !(bound_vars.contains(v) || free_vars.contains(v)) {
                        free_vars.push(*v);
                    }
                    decr(&mut var_stack, &mut bound_vars)
                }
                RichFormula::Fun(_, args) => {
                    // quantifier are taken care of automatically
                    incr(&mut var_stack, &mut bound_vars, todo, args.as_ref())
                }
                RichFormula::Quantifier(q, formula) => {
                    add_vars(&mut bound_vars, &mut var_stack, q.get_variables());
                    todo.push(formula.as_ref())
                }
            }
        }
    }

    /// doesn't go though all quantifiers
    pub fn get_used_variables(&'_ self) -> HashSet<Variable<'bump>> {
        fn aux<'a, 'bump>(data: &mut HashSet<Variable<'bump>>, f: &RichFormula<'bump>) {
            match f {
                RichFormula::Var(v) => {
                    data.insert(*v);
                }
                RichFormula::Fun(_, args) => args.iter().for_each(|f| aux(data, f.as_ref())),
                RichFormula::Quantifier(q, args) => {
                    data.extend(q.get_variables().iter().cloned());
                    // args.iter().for_each(|f| aux(data, f))
                    aux(data, args.as_ref())
                }
            }
        }

        let mut data = HashSet::new();
        aux(&mut data, self);
        data
    }

    pub fn map<F>(self, f: &mut F) -> ARichFormula<'bump>
    where
        F: FnMut(Self) -> ARichFormula<'bump>,
    {
        match self {
            RichFormula::Var(_) => f(self),
            RichFormula::Fun(fun, args) => {
                let tmp = Self::Fun(
                    fun,
                    args.into_iter()
                        .map(|x| x.into_inner().map(f))
                        .map_into()
                        .collect(),
                );
                f(tmp)
            }
            RichFormula::Quantifier(q, args) => {
                let tmp = Self::Quantifier(
                    q,
                    // args.into_iter().map(|x| x.map(f)).collect(),
                    args.owned_into_inner().map(f),
                );
                f(tmp)
            }
        }
    }

    pub fn apply<F>(self, mut f: F) -> ARichFormula<'bump>
    where
        F: FnMut(&Variable<'bump>) -> ARichFormula<'bump>,
    {
        self.map(&mut {
            |form| match form {
                Self::Var(v) => f(&v),
                _ => form.into(),
            }
        })
    }

    pub fn apply_some<F>(self, f: F) -> ARichFormula<'bump>
    where
        F: Fn(&Variable<'bump>) -> Option<ARichFormula<'bump>>,
    {
        self.apply(|v: &Variable| f(v).unwrap_or(v.into()))
    }

    pub fn apply_substitution<'a>(
        self,
        vars: implvec!(usize),
        fs: implvec!(&'a ARichFormula<'bump>),
    ) -> ARichFormula<'bump>
    where
        'bump: 'a,
    {
        let vars = vars.into_iter().collect_vec();
        let fs = fs.into_iter().collect_vec();
        if cfg!(debug_assertions) && vars.len() != fs.len() {
            panic!("assertion failed:\n{vars:?}\n[{}]", fs.iter().join(", "))
        }
        self.apply_some(|v| {
            vars.iter()
                .position(|v2| v2 == &v.id)
                .map(|i| fs[i].clone())
        })
    }

    pub fn apply_substitution2(&self, per: &impl Substitution<'bump>) -> ARichFormula<'bump> {
        per.apply(self)
    }

    pub fn translate_vars(&self, i: usize) -> Self {
        self.apply_substitution2(&Translate::new(i))
            .owned_into_inner()
    }

    // pub fn smt(&self) -> SmtFormula {
    //     self.into()
    // }

    pub fn expand_clone(
        &self,
        ptcl: &Protocol<'bump>,
        with_args: bool,
        deeper_kind: DeeperKinds,
    ) -> Vec<ExpantionContent<'bump>> {
        ExpantionContent {
            state: ExpantionState::None,
            content: self.into(),
        }
        .expand(
            ptcl.steps().iter().cloned(),
            ptcl.graph(),
            with_args,
            deeper_kind,
        )
    }

    pub fn into_arc(self) -> ARichFormula<'bump> {
        self.into()
    }

    /// Returns `true` if the rich formula is [`Var`].
    ///
    /// [`Var`]: RichFormula::Var
    #[must_use]
    pub fn is_var(&self) -> bool {
        matches!(self, Self::Var(..))
    }

    /// Returns `true` if the rich formula is [`Fun`].
    ///
    /// [`Fun`]: RichFormula::Fun
    #[must_use]
    pub fn is_fun(&self) -> bool {
        matches!(self, Self::Fun(..))
    }

    /// Returns `true` if the rich formula is [`Quantifier`].
    ///
    /// [`Quantifier`]: RichFormula::Quantifier
    #[must_use]
    pub fn is_quantifier(&self) -> bool {
        matches!(self, Self::Quantifier(..))
    }

    pub fn clone_as_arc(&self) -> ARichFormula<'bump> {
        self.into()
    }
}

// pub trait AFormula<'bump> {
//     fn expand(
//         &self,
//         ptcl: &Protocol<'bump>,
//         with_args: bool,
//         deeper_kind: DeeperKinds,
//     ) -> Vec<ExpantionContent<'bump>>;

//     fn iter_with_pile<'a, V>(
//         &'a self,
//         mut pile: V,
//     ) -> impl Iterator<Item = &'a RichFormula<'bump>>
//     where
//         V: DerefMut<Target = Vec<((), &'a Self)>> + Deref<Target = Vec<((), &'a Self)>>;
// }

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

impl<'bump> Display for RichFormula<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RichFormula::Var(v) => v.fmt(f),
            RichFormula::Fun(fun, args) => {
                write!(f, "{}({})", fun.name(), args.iter().join(", "))
            }
            RichFormula::Quantifier(q, arg) => write!(f, "{q} {arg}"),
        }
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
    arg: impl Into<ARichFormula<'bump>>,
) -> ARichFormula<'bump> {
    let mut vars = vars.into_iter().peekable();
    if let Some(_) = vars.peek() {
        // let variables = vars.collect_vec();
        RichFormula::Quantifier(Quantifier::forall(vars), arg.into()).into()
    } else {
        arg.into()
    }
}

pub fn exists<'bump>(
    vars: impl IntoIterator<Item = Variable<'bump>>,
    arg: impl Into<ARichFormula<'bump>>,
) -> ARichFormula<'bump> {
    let mut vars = vars.into_iter().peekable();
    if let Some(_) = vars.peek() {
        // let variables = vars.collect_vec();
        RichFormula::Quantifier(Quantifier::exists(vars), arg.into()).into()
    } else {
        arg.into()
    }
}

pub fn meq<'bump>(
    lhs: impl Into<ARichFormula<'bump>>,
    rhs: impl Into<ARichFormula<'bump>>,
) -> ARichFormula<'bump> {
    EQUALITY.f_a([lhs.into(), rhs.into()])
}

pub fn ands<'bump>(args: impl IntoIterator<Item = ARichFormula<'bump>>) -> ARichFormula<'bump> {
    AND.f_a(args)
}

pub fn ors<'bump>(args: impl IntoIterator<Item = ARichFormula<'bump>>) -> ARichFormula<'bump> {
    OR.f_a(args)
}

pub fn ands_owned<'bump>(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
    AND.f(args)
}

pub fn ors_owned<'bump>(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
    OR.f(args)
}
