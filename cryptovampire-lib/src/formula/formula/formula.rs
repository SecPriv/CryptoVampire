use std::{
    fmt::Display,
    ops::{BitAnd, BitOr, Not, Shr},
    sync::Arc,
};

use hashbrown::HashSet;
use itertools::Itertools;

use crate::formula::{
    formula::ARichFormula, function::{
        builtin::{AND, EQUALITY, IMPLIES, NOT, OR},
        signature::Signature,
        Function,
    }, manipulation::{Substitution, Translate}, quantifier::Quantifier, sort::{
        builtins::BOOL,
        sorted::{Sorted, SortedError},
        Sort,
    }, utils::formula_iterator::FormulaIterator, variable::{uvar, IntoVariableIter, Variable}
};
use utils::implvec;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Arc<[ARichFormula<'bump>]>), //Vec<RichFormula<'bump>>),
    Quantifier(Quantifier<'bump>, ARichFormula<'bump>),
}

impl<'bump> RichFormula<'bump> {
    pub fn get_sort(&self) -> Result<Sort<'bump>, SortedError> {
        // trace!("  checksort -> {self}");
        match self {
            RichFormula::Var(Variable { sort, .. }) => Ok(*sort),
            RichFormula::Fun(fun, args) => {
                if let Some(s) = fun.signature().out().as_option() {
                    return Ok(s);
                }
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
        vars: implvec!(uvar),
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

    pub fn translate_vars(&self, i: uvar) -> Self {
        self.apply_substitution2(&Translate::new(i))
            .owned_into_inner()
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

    #[must_use]
    pub fn as_var(&self) -> Option<&Variable<'bump>> {
        if let Self::Var(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl<'bump> AsRef<Self> for RichFormula<'bump> {
    fn as_ref(&self) -> &Self {
        self
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

#[cfg(test)]
mod tests {
    use crate::{
        formula::{
            formula::ARichFormula,
            function::builtin::CONDITION_TO_BOOL,
            sort::builtins::{BOOL, CONDITION, STEP},
            variable::Variable,
        },
        mexists, mforall,
    };

    use super::meq;

    #[test]
    fn free_vars() {
        let [v1, v2, v3, v4] = [
            (1, BOOL.as_sort()),
            (57, BOOL.as_sort()),
            (3, STEP.as_sort()),
            (4, CONDITION.as_sort()),
        ]
        .map(|(id, sort)| Variable { id, sort });

        let formula = CONDITION_TO_BOOL.f_a([&v4])
            >> mforall!(a!346:STEP.as_sort(); {
                ARichFormula::from(&v1) & (v2.into())
                    & mexists!(s!4398:STEP.as_sort(); {
                        meq(&v3, s)
                    })
            });

        let mut vars = [v1, v2, v3, v4];
        vars.sort();

        let mut fvars = formula.get_free_vars();
        fvars.sort();

        assert_eq!(&vars, fvars.as_slice())
    }
}
