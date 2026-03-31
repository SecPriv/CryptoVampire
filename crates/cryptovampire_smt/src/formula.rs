use std::borrow::Cow;
use std::collections::VecDeque;
use std::fmt::Display;
use std::iter::once;
use std::ops::{BitAnd, BitOr, Not, Shr};
use std::sync::Arc;

use itertools::Itertools;
use logic_formula::{AsFormula, Bounder, Destructed, HeadSk};
use quarck::CowArc;
use rustc_hash::FxHashSet;
use utils::{dynamic_iter, ebreak_if, ereturn_if, implvec};

use super::SortedVar;
use crate::solvers::SolverFeatures;
use crate::{CheckError, SmtParam, SolverKind, write_list, write_par};

/// Represents an SMT formula.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SmtFormula<'a, U: SmtParam + 'a> {
    /// A variable.
    Var(U::SVar),
    /// A function application.
    Fun(U::Function, CowArc<'a, [Self]>),
    /// A universal quantifier.
    Forall(CowArc<'a, [U::SVar]>, CowArc<'a, Self>),
    /// An existential quantifier.
    Exists(CowArc<'a, [U::SVar]>, CowArc<'a, Self>),

    /// The boolean literal `true`.
    True,
    /// The boolean literal `false`.
    False,
    /// A conjunction of formulas.
    And(CowArc<'a, [Self]>),
    /// A disjunction of formulas.
    Or(CowArc<'a, [Self]>),
    /// An equality of terms.
    Eq(CowArc<'a, [Self]>),
    /// A disequality of terms.
    Neq(CowArc<'a, [Self]>),
    /// A negation of a formula.
    Not(CowArc<'a, Self>),
    /// An implication.
    Implies(CowArc<'a, [Self; 2]>),

    /// An if-then-else expression.
    Ite(CowArc<'a, [Self; 3]>),

    #[cfg(feature = "cryptovampire")]
    /// A subterm assertion (specific to cryptovampire).
    Subterm(U::Function, CowArc<'a, [Self; 2]>),
}

impl<'a, U: SmtParam> Clone for SmtFormula<'a, U>
where
    U::SVar: Clone,
    U::Function: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Var(arg0) => Self::Var(arg0.clone()),
            Self::Fun(arg0, arg1) => Self::Fun(arg0.clone(), arg1.clone()),
            Self::Forall(arg0, arg1) => Self::Forall(arg0.clone(), arg1.clone()),
            Self::Exists(arg0, arg1) => Self::Exists(arg0.clone(), arg1.clone()),
            Self::True => Self::True,
            Self::False => Self::False,
            Self::And(arg0) => Self::And(arg0.clone()),
            Self::Or(arg0) => Self::Or(arg0.clone()),
            Self::Eq(arg0) => Self::Eq(arg0.clone()),
            Self::Neq(arg0) => Self::Neq(arg0.clone()),
            Self::Not(arg0) => Self::Not(arg0.clone()),
            Self::Implies(arg0) => Self::Implies(arg0.clone()),
            Self::Ite(arg0) => Self::Ite(arg0.clone()),
            #[cfg(feature = "cryptovampire")]
            Self::Subterm(arg0, arg1) => Self::Subterm(arg0.clone(), arg1.clone()),
        }
    }
}

/// Represents the head of an SMT formula, indicating the type of operation.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtHead {
    /// The boolean literal `true`.
    True,
    /// The boolean literal `false`.
    False,
    /// Conjunction.
    And,
    /// Disjunction.
    Or,
    /// Equality.
    Eq,
    /// Disequality.
    Neq,
    /// Negation.
    Not,
    /// Implication.
    Implies,
    /// If-then-else.
    If,
}

/// Represents an SMT quantifier with its bound variables.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SmtQuantifier<'a, U: SmtParam> {
    /// Universal quantifier.
    Forall(CowArc<'a, [U::SVar]>),
    /// Existential quantifier.
    Exists(CowArc<'a, [U::SVar]>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtQuantifierRef<'a, U: SmtParam> {
    /// Universal quantifier.
    Forall(&'a [U::SVar]),
    /// Existential quantifier.
    Exists(&'a [U::SVar]),
}

impl<'a, U: SmtParam> Default for SmtFormula<'a, U> {
    /// Returns the default SMT formula, which is `True`.
    fn default() -> Self {
        Self::True
    }
}

/// Helper function to write an SMT application (head and arguments).
fn write_app<U>(f: &mut std::fmt::Formatter<'_>, head: &str, args: implvec!(U)) -> std::fmt::Result
where
    U: Display,
{
    write_par(f, |f| {
        write!(f, "{head} ")?;
        for arg in args {
            write!(f, "{arg} ")?;
        }
        Ok(())
    })
}

impl<'a, U> Display for SmtFormula<'a, U>
where
    U: SmtParam,
{
    /// Formats the SMT formula for display in SMT-LIB format.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SmtFormula::Var(v) => write!(f, "{v}"),
            SmtFormula::Fun(fun, smt_formulas) => {
                if smt_formulas.is_empty() {
                    write!(f, "{fun}")
                } else {
                    write!(f, "({fun}")?;
                    for arg in smt_formulas.iter() {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            SmtFormula::Forall(vars, formula) => write_par(f, |f| {
                write!(f, "forall ")?;
                write_list(vars.iter(), f, |f, var| {
                    write!(f, "({var} {}) ", var.sort_ref())
                })?;
                write!(f, "{formula}")
            }),
            SmtFormula::Exists(vars, formula) => write_par(f, |f| {
                write!(f, "exists ")?;
                write_list(vars.iter(), f, |f, var| {
                    write!(f, "({var} {}) ", var.sort_ref())
                })?;
                write!(f, "{formula}")
            }),
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) => write_app(f, "and", args.iter()),
            SmtFormula::Or(args) => write_app(f, "or", args.iter()),
            SmtFormula::Eq(args) => write_app(f, "=", args.iter()),
            SmtFormula::Neq(args) => write_app(f, "distinct", args.iter()),
            SmtFormula::Not(args) => write!(f, "(not {args})"),
            SmtFormula::Implies(args) => write_app(f, "=>", args.iter()),
            SmtFormula::Ite(args) => write_app(f, "ite", args.iter()),

            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(fun, args) => {
                writeln!(
                    f,
                    "\n; cryptovampire specific. Needs a modified version of vampire"
                )?;
                let [a, b] = args.as_ref();
                write!(f, "(subterm {fun} {a} {b})")
            }
        }
    }
}

impl<'a, U: SmtParam> SmtFormula<'a, U> {
    /// Creates a builtin SMT formula from a given `SmtHead` and arguments.
    pub fn builtin(head: SmtHead, args: implvec!(Self)) -> Result<Self, Vec<Self>> {
        let args: Vec<_> = args.into_iter().collect();
        use SmtFormula::*;
        match head {
            SmtHead::True => {
                ereturn_if!(!args.is_empty(), Err(args));
                Ok(True)
            }
            SmtHead::False => {
                ereturn_if!(!args.is_empty(), Err(args));
                Ok(False)
            }
            SmtHead::And => Ok(And(args.into())),
            SmtHead::Or => Ok(Or(args.into())),
            SmtHead::Eq => Ok(Eq(args.into())),
            SmtHead::Neq => Ok(Neq(args.into())),
            SmtHead::Not => {
                let [arg] = args.try_into()?;
                Ok(Not(enbox(arg)))
            }
            SmtHead::Implies => Ok(Implies(enbox(args.try_into()?))),
            SmtHead::If => Ok(Ite(enbox(args.try_into()?))),
        }
    }

    /// Optimises the SMT formula in-place.
    fn optimise_mut(&mut self)
    where
        U::SVar: Eq + Clone,
        U::Function: Clone,
    {
        match self {
            SmtFormula::Fun(_, args) | SmtFormula::Eq(args) | SmtFormula::Neq(args) => {
                args.to_mut_slice().iter_mut().for_each(Self::optimise_mut);
            }
            // smt-lib assumes non-empty sorts (sec 5.3 def 6)
            // This remove
            SmtFormula::Forall(vars, f) | SmtFormula::Exists(vars, f) => {
                let f = f.to_mut();
                f.optimise_mut();
                let mut vec_vars = vars.to_vec();

                optimize_variables_quantifiers(&mut vec_vars, f);

                if vec_vars.is_empty() {
                    // gymnastic to set `self` to `f`
                    *self = ::std::mem::take(f);
                } else {
                    *vars = CowArc::from_vec(vec_vars);
                }
            }
            SmtFormula::And(args_cow) => {
                let mut args = args_cow.to_vec();
                let mut i = 0;

                loop {
                    if let Some(Self::And(_)) = args.get(i) {
                        let Self::And(args_deep) = args.swap_remove(i) else {
                            unreachable!()
                        };
                        args.extend_from_slice(&args_deep);
                    }

                    ebreak_if!(i >= args.len());

                    let arg = &mut args[i];
                    arg.optimise_mut();

                    if arg.is_false() {
                        *self = Self::False;
                        return;
                    } else if arg.is_true() {
                        args.swap_remove(i);
                        continue;
                    }
                    i += 1
                }

                if args.is_empty() {
                    *self = Self::True;
                } else if args.len() == 1 {
                    *self = ::std::mem::take(&mut args[0]);
                } else {
                    *args_cow = CowArc::from_vec(args)
                }
            }
            SmtFormula::Or(args_cow) => {
                let mut args = args_cow.to_vec();
                let mut i = 0;

                loop {
                    if let Some(Self::Or(_)) = args.get(i) {
                        let Self::Or(args_deep) = args.swap_remove(i) else {
                            unreachable!()
                        };
                        args.extend_from_slice(&args_deep);
                    }

                    ebreak_if!(i >= args.len());

                    let arg = &mut args[i];
                    arg.optimise_mut();

                    if arg.is_true() {
                        *self = Self::True;
                        return;
                    } else if arg.is_false() {
                        args.swap_remove(i);
                        continue;
                    }
                    i += 1
                }

                if args.is_empty() {
                    *self = Self::False;
                } else if args.len() == 1 {
                    *self = ::std::mem::take(&mut args[0]);
                } else {
                    *args_cow = CowArc::from_vec(args)
                }
            }
            SmtFormula::Implies(args) => {
                let [a, b] = args.to_mut();
                a.optimise_mut();
                if a.is_false() {
                    *self = Self::True;
                    return;
                }
                b.optimise_mut();
                if a.is_true() || b.is_true() {
                    *self = ::std::mem::take(b);
                }
            }
            SmtFormula::Ite(args) => {
                let [c, l, r] = args.to_mut();
                c.optimise_mut();
                if c.is_true() {
                    l.optimise_mut();
                    *self = ::std::mem::take(l);
                    return;
                } else if c.is_false() {
                    r.optimise_mut();
                    *self = ::std::mem::take(r);
                    return;
                }
                l.optimise_mut();
                r.optimise_mut();
            }
            _ => (),
        }
    }

    /// Optimises the SMT formula and returns the optimised version.
    pub fn optimise(mut self) -> Self
    where
        U::SVar: Eq,
    {
        self.optimise_mut();
        self
    }

    /// Returns `true` if the smt formula is [`True`].
    ///
    /// [`True`]: SmtFormula::True
    #[must_use]
    pub const fn is_true(&self) -> bool {
        matches!(self, Self::True)
    }

    /// Returns `true` if the smt formula is [`False`].
    ///
    /// [`False`]: SmtFormula::False
    #[must_use]
    pub const fn is_false(&self) -> bool {
        matches!(self, Self::False)
    }

    pub fn check(&self, kind: SolverKind) -> Result<(), CheckError> {
        match self {
            Self::True | Self::False | Self::Var(_) => Ok(()),
            Self::Forall(vars, arg) | Self::Exists(vars, arg) => {
                if vars.is_empty() {
                    Err(CheckError::EmptyQuantifier)
                } else {
                    arg.check(kind)
                }
            }
            Self::Fun(_, f) | Self::And(f) | Self::Or(f) | Self::Eq(f) | Self::Neq(f) => {
                Self::rec_check(f.iter(), kind)
            }
            Self::Ite(args) => Self::rec_check(args.iter(), kind),
            #[cfg(feature = "cryptovampire")]
            Self::Subterm(_, args) => {
                if !kind.contains(SolverKind::CVSubterm) {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::Subterm))
                } else {
                    Self::rec_check(args.iter(), kind)
                }
            }
            Self::Implies(args) => Self::rec_check(args.iter(), kind),
            Self::Not(f) => f.check(kind),
        }
    }

    fn rec_check<'b>(selves: implvec!(&'b Self), kind: SolverKind) -> Result<(), CheckError>
    where
        U: 'b,
        'a: 'b,
    {
        for f in selves {
            f.check(kind)?
        }
        Ok(())
    }
}

fn optimize_variables_quantifiers<'a, U>(vars: &mut Vec<U::SVar>, f: &SmtFormula<'a, U>)
where
    U: SmtParam,
    U::SVar: std::cmp::Eq,
{
    ereturn_if!(vars.is_empty());
    // bvar is the indices of `vars` which have relevant variables, the rest can be discarded
    let mut bvars = f
        .free_vars_iter()
        .filter_map(|fv| vars.iter().position(|v| v == fv))
        .collect_vec();
    bvars.sort_unstable();
    bvars.dedup();
    let mut bvars = bvars.as_slice();
    // in-place filters out the unnessesary variables from `vars`
    let mut i = 0;
    while i < vars.len() {
        let Some(&fst) = bvars.first() else {
            vars.truncate(i);
            return;
        };
        if i < fst {
            vars.swap_remove(i);
            bvars = &bvars[0..bvars.len() - 1];
            // we keep vars[i]
        } else if i == fst {
            bvars = &bvars[1..];
        } else {
            unreachable!()
        }
        i += 1;
    }
}

// /// A trait for types that can be converted into an SMT formula.
// pub trait IntoSmt<U: SmtParam>: AsFormula {
//     /// Converts a generic function into an SMT function.
//     fn convert_function(fun: Self::Fun) -> U::Function;
//     /// Converts a generic variable into an SMT sorted variable.
//     fn convert_var(var: Self::Var) -> <U as SmtParam>::SVar;
//     /// Converts a generic quantifier into an SMT quantifier.
//     fn convert_quant(quant: Self::Quant) -> SmtQuantifier<U>;
//     /// Converts a generic function head into an SMT head, if applicable.
//     fn as_head(fun: &Self::Fun) -> Option<SmtHead>;

//     /// Converts the formula into an SMT formula.
//     fn into_smt(self) -> SmtFormula<U> {
//         SmtFormula::from_formula(self)
//     }
// }

/// Represents either a builtin SMT function or a user-defined function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtFunctions<F> {
    /// A builtin SMT function.
    Smt(SmtHead),
    /// A user-defined function.
    Fun(F),
}

impl<F> From<F> for SmtFunctions<F> {
    /// Converts a function `F` into an `SmtFunctions::Fun` variant.
    fn from(v: F) -> Self {
        Self::Fun(v)
    }
}

impl<'a, U: SmtParam> AsFormula for SmtFormula<'a, U> {
    /// The variable type for the formula.
    type Var = U::SVar;

    /// The function type for the formula.
    type Fun = SmtFunctions<U::Function>;

    /// The quantifier type for the formula.
    type Quant = SmtQuantifier<'a, U>;

    /// Destructures the SMT formula into its head and arguments.
    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; None:A, One:B, Map:D);

        let mk = |h| HeadSk::Fun(SmtFunctions::Smt(h));

        use SmtHead::*;
        match self {
            SmtFormula::Var(v) => Destructed {
                head: HeadSk::Var(v),
                args: MIter::None(::std::iter::empty()),
            },
            SmtFormula::Fun(f, args) => Destructed {
                head: HeadSk::Fun(f.into()),
                args: MIter::Map(args.into_cloned_iter()),
            },
            SmtFormula::Forall(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifier::Forall(vars)),
                args: MIter::One(once(f.into_inner())),
            },
            SmtFormula::Exists(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifier::Exists(vars)),
                args: MIter::One(once(f.into_inner())),
            },
            SmtFormula::True => Destructed {
                head: mk(True),
                args: MIter::None(Default::default()),
            },
            SmtFormula::False => Destructed {
                head: mk(False),
                args: MIter::None(Default::default()),
            },
            SmtFormula::And(args) => Destructed {
                head: mk(And),
                args: MIter::Map(args.into_cloned_iter()),
            },
            SmtFormula::Or(args) => Destructed {
                head: mk(Or),
                args: MIter::Map(args.into_cloned_iter()),
            },
            SmtFormula::Eq(args) => Destructed {
                head: mk(Eq),
                args: MIter::Map(args.into_cloned_iter()),
            },
            SmtFormula::Neq(args) => Destructed {
                head: mk(Neq),
                args: MIter::Map(args.into_cloned_iter()),
            },
            SmtFormula::Not(arg) => Destructed {
                head: mk(Not),
                args: MIter::One(once(arg.into_inner())),
            },
            SmtFormula::Implies(args) => Destructed {
                head: mk(Implies),
                args: MIter::Map(args.forget_size().into_cloned_iter()),
            },
            SmtFormula::Ite(args) => Destructed {
                head: mk(If),
                args: MIter::Map(args.forget_size().into_cloned_iter()),
            },
            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(_, _) => unimplemented!(),
        }
    }
}

impl<'b, 'a: 'b, U: SmtParam> AsFormula for &'a SmtFormula<'b, U> {
    /// The variable type for the formula.
    type Var = &'a U::SVar;

    /// The function type for the formula.
    type Fun = SmtFunctions<&'a U::Function>;

    /// The quantifier type for the formula.
    type Quant = SmtQuantifierRef<'a, U>;

    /// Destructures the SMT formula into its head and arguments.
    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; None:A, One:B, Ref:D);

        let mk = |h| HeadSk::Fun(SmtFunctions::Smt(h));

        use SmtHead::*;
        match self {
            SmtFormula::Var(v) => Destructed {
                head: HeadSk::Var(v),
                args: MIter::None(::std::iter::empty()),
            },
            SmtFormula::Fun(f, args) => Destructed {
                head: HeadSk::Fun(f.into()),
                args: MIter::Ref(args.iter()),
            },
            SmtFormula::Forall(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifierRef::Forall(vars.as_ref())),
                args: MIter::One(once(f.as_ref())),
            },
            SmtFormula::Exists(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifierRef::Exists(vars.as_ref())),
                args: MIter::One(once(f.as_ref())),
            },
            SmtFormula::True => Destructed {
                head: mk(True),
                args: MIter::None(Default::default()),
            },
            SmtFormula::False => Destructed {
                head: mk(False),
                args: MIter::None(Default::default()),
            },
            SmtFormula::And(args) => Destructed {
                head: mk(And),
                args: MIter::Ref(args.iter()),
            },
            SmtFormula::Or(args) => Destructed {
                head: mk(Or),
                args: MIter::Ref(args.iter()),
            },
            SmtFormula::Eq(args) => Destructed {
                head: mk(Eq),
                args: MIter::Ref(args.iter()),
            },
            SmtFormula::Neq(args) => Destructed {
                head: mk(Neq),
                args: MIter::Ref(args.iter()),
            },
            SmtFormula::Not(arg) => Destructed {
                head: mk(Not),
                args: MIter::One(once(arg.as_ref())),
            },
            SmtFormula::Implies(args) => {
                let args: &[SmtFormula<'b, U>] = args.as_ref().as_slice();
                Destructed {
                    head: mk(Implies),
                    args: MIter::Ref(args.iter()),
                }
            }
            SmtFormula::Ite(args) => {
                let args: &[SmtFormula<'b, U>] = args.as_ref().as_slice();
                Destructed {
                    head: mk(If),
                    args: MIter::Ref(args.iter()),
                }
            }
            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(_, _) => unimplemented!(),
        }
    }
}

impl<'a, U: SmtParam> Not for SmtFormula<'a, U> {
    /// The output type of the negation operation.
    type Output = Self;

    /// Applies logical negation to the SMT formula.
    fn not(self) -> Self::Output {
        Self::Not(enbox(self))
    }
}

impl<'a, U: SmtParam> BitAnd for SmtFormula<'a, U> {
    /// The output type of the bitwise AND operation.
    type Output = Self;

    /// Applies logical AND to two SMT formulas.
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::And([self, rhs].into())
    }
}

impl<'a, U: SmtParam> BitOr for SmtFormula<'a, U> {
    /// The output type of the bitwise OR operation.
    type Output = Self;

    /// Applies logical OR to two SMT formulas.
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Or([self, rhs].into())
    }
}

impl<'a, U: SmtParam> Shr for SmtFormula<'a, U> {
    /// The output type of the right shift operation (used for implication).
    type Output = Self;

    /// Applies logical implication to two SMT formulas.
    fn shr(self, rhs: Self) -> Self::Output {
        Self::Implies([self, rhs].into())
    }
}

impl<'a, U: SmtParam> Bounder<&'a U::SVar> for SmtQuantifierRef<'a, U> {
    /// Returns an iterator over the bound variables of the quantifier.
    fn bounds(&self) -> impl Iterator<Item = &'a U::SVar> {
        match self {
            Self::Forall(vars) | Self::Exists(vars) => vars.iter(),
        }
    }
}

#[inline]
fn enbox<'a, A>(x: A) -> CowArc<'a, A> {
    x.into()
}
