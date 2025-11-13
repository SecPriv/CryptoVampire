use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Not, Shr};
use std::sync::Arc;

use itertools::{Either, Itertools};
use logic_formula::{Destructed, Head};
use utils::implvec;
use utils::utils::MaybeInvalid;

use crate::formula::formula::ARichFormula;
use crate::formula::function::Function;
use crate::formula::function::builtin::{AND, EQUALITY, IMPLIES, NOT, OR};
use crate::formula::function::signature::Signature;
use crate::formula::manipulation::{Substitution, Translate};
use crate::formula::quantifier::Quantifier;
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::BOOL;
use crate::formula::sort::sorted::{Sorted, SortedError};
use crate::formula::utils::Applicable;
use crate::formula::variable::{Variable, uvar};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum RichFormula<'bump> {
    Var(Variable<'bump>),
    Fun(Function<'bump>, Arc<[ARichFormula<'bump>]>), // Vec<RichFormula<'bump>>),
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

    pub fn map<F>(self, f: &mut F) -> ARichFormula<'bump>
    where
        F: FnMut(Self) -> ARichFormula<'bump>,
    {
        match self {
            RichFormula::Var(_) => f(self),
            RichFormula::Fun(fun, args) => {
                let tmp = Self::Fun(
                    fun,
                    args.iter()
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
        self.apply(|v| f(v).unwrap_or(v.into()))
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
        (*v).into()
    }
}

impl<'bump> BitAnd for RichFormula<'bump> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        AND.apply([self, rhs])
    }
}

impl<'bump> BitOr for RichFormula<'bump> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        OR.apply([self, rhs])
    }
}

impl<'bump> Not for RichFormula<'bump> {
    type Output = Self;

    fn not(self) -> Self::Output {
        NOT.apply([self])
    }
}

impl<'bump> Shr for RichFormula<'bump> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        IMPLIES.apply([self, rhs])
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

impl<'bump> MaybeInvalid for RichFormula<'bump> {
    fn is_valid(&self) -> bool {
        match self {
            RichFormula::Var(v) => v.is_valid(),
            RichFormula::Fun(f, args) => f.is_valid() && args.iter().all(MaybeInvalid::is_valid),
            RichFormula::Quantifier(_, arg) => arg.is_valid(),
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
    if vars.peek().is_some() {
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
    if vars.peek().is_some() {
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
    EQUALITY.f([lhs.into(), rhs.into()])
}

pub fn ands<'bump>(args: impl IntoIterator<Item = ARichFormula<'bump>>) -> ARichFormula<'bump> {
    AND.f(args)
}

pub fn ors<'bump>(args: impl IntoIterator<Item = ARichFormula<'bump>>) -> ARichFormula<'bump> {
    OR.f(args)
}

pub fn ands_owned<'bump>(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
    AND.apply(args)
}

pub fn ors_owned<'bump>(args: impl IntoIterator<Item = RichFormula<'bump>>) -> RichFormula<'bump> {
    OR.apply(args)
}

impl<'a, 'bump> logic_formula::AsFormula for &'a RichFormula<'bump> {
    type Var = Variable<'bump>;

    type Fun = Function<'bump>;

    type Quant = Quantifier<'bump>;

    fn destruct(self) -> logic_formula::Destructed<Self, impl Iterator<Item = Self>> {
        match self {
            RichFormula::Var(v) => Destructed {
                head: Head::<&'a RichFormula<'bump>>::Var(*v),
                args: Either::Left(std::iter::empty()),
            },
            RichFormula::Fun(f, args) => Destructed {
                head: Head::<&'a RichFormula<'bump>>::Fun(*f),
                args: Either::Right(Either::Left(args.iter().map(|a| a.as_ref()))),
            },
            RichFormula::Quantifier(q, arg) => Destructed {
                head: Head::<&'a RichFormula<'bump>>::Quant(q.clone()),
                args: Either::Right(Either::Right([arg.as_ref()].into_iter())),
            },
        }
    }
}

impl<'a, 'bump> crate::error::LocationProvider for &'a RichFormula<'bump> {
    fn provide(self) -> crate::error::Location {
        crate::error::Location::from_display(self)
    }
}

#[cfg(test)]
mod tests {
    use itertools::Itertools;
    use logic_formula::AsFormula;

    use super::meq;
    use crate::formula::formula::ARichFormula;
    use crate::formula::function::builtin::CONDITION_TO_BOOL;
    use crate::formula::sort::builtins::{BOOL, CONDITION, STEP};
    use crate::formula::utils::Applicable;
    use crate::formula::variable::Variable;
    use crate::{mexists, mforall};

    #[test]
    fn free_vars() {
        let [v1, v2, v3, v4] = [
            (1, BOOL.as_sort()),
            (57, BOOL.as_sort()),
            (3, STEP.as_sort()),
            (4, CONDITION.as_sort()),
        ]
        .map(|(id, sort)| Variable { id, sort });

        let formula = CONDITION_TO_BOOL.f([&v4])
            >> mforall!(a!346:STEP.as_sort(); {
                ARichFormula::from(&v1) & (v2.into())
                    & mexists!(s!4398:STEP.as_sort(); {
                        meq(v3, s)
                    })
            });

        let mut vars = [v1, v2, v3, v4];
        vars.sort();

        let fvars = formula.free_vars_iter().unique().sorted().collect_vec();

        assert_eq!(&vars, fvars.as_slice())
    }
}
