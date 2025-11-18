use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Not, Shr};

use itertools::Itertools;
use logic_formula::{AsFormula, Bounder, Destructed, HeadSk};
use utils::{dynamic_iter, ereturn_if, implvec};

use super::SortedVar;
use crate::{SmtParam, write_list, write_par};

/// Represents an SMT formula.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<U: SmtParam> {
    /// A variable.
    Var(U::SVar),
    /// A function application.
    Fun(U::Function, Vec<SmtFormula<U>>),
    /// A universal quantifier.
    Forall(Vec<U::SVar>, Box<SmtFormula<U>>),
    /// An existential quantifier.
    Exists(Vec<U::SVar>, Box<SmtFormula<U>>),

    /// The boolean literal `true`.
    True,
    /// The boolean literal `false`.
    False,
    /// A conjunction of formulas.
    And(Vec<SmtFormula<U>>),
    /// A disjunction of formulas.
    Or(Vec<SmtFormula<U>>),
    /// An equality of terms.
    Eq(Vec<SmtFormula<U>>),
    /// A disequality of terms.
    Neq(Vec<SmtFormula<U>>),
    /// A negation of a formula.
    Not(Box<SmtFormula<U>>),
    /// An implication.
    Implies(Box<SmtFormula<U>>, Box<SmtFormula<U>>),

    /// An if-then-else expression.
    Ite(Box<SmtFormula<U>>, Box<SmtFormula<U>>, Box<SmtFormula<U>>),

    #[cfg(feature = "cryptovampire")]
    /// A subterm assertion (specific to cryptovampire).
    Subterm(U::Function, Box<SmtFormula<U>>, Box<SmtFormula<U>>),
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
pub enum SmtQuantifier<U: SmtParam> {
    /// Universal quantifier.
    Forall(Vec<U::SVar>),
    /// Existential quantifier.
    Exists(Vec<U::SVar>),
}

/// Represents an SMT quantifier with references to its bound variables.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtQuantifierRef<'a, U: SmtParam> {
    /// Universal quantifier with references to bound variables.
    Forall(&'a [U::SVar]),
    /// Existential quantifier with references to bound variables.
    Exists(&'a [U::SVar]),
}

impl<U: SmtParam> Default for SmtFormula<U> {
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

impl<U> Display for SmtFormula<U>
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
                    for arg in smt_formulas {
                        write!(f, " {arg}")?;
                    }
                    write!(f, ")")
                }
            }
            SmtFormula::Forall(vars, formula) => write_par(f, |f| {
                write!(f, "forall ")?;
                write_list(vars, f, |f, var| write!(f, "({var} {}) ", var.sort_ref()))?;
                write!(f, "{formula}")
            }),
            SmtFormula::Exists(vars, formula) => write_par(f, |f| {
                write!(f, "exists ")?;
                write_list(vars, f, |f, var| write!(f, "({var} {}) ", var.sort_ref()))?;
                write!(f, "{formula}")
            }),
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) => write_app(f, "and", args),
            SmtFormula::Or(args) => write_app(f, "or", args),
            SmtFormula::Eq(args) => write_app(f, "=", args),
            SmtFormula::Neq(args) => write_app(f, "distinct", args),
            SmtFormula::Not(args) => write!(f, "(not {args})"),
            SmtFormula::Implies(premise, conclusion) => write!(f, "(=> {premise} {conclusion})"),
            SmtFormula::Ite(c, l, r) => write!(f, "(ite {c} {l} {r})"),

            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(fun, a, b) => {
                writeln!(
                    f,
                    "\n; cryptovampire specific. Needs a modified version of vampire"
                )?;
                write!(f, "(subterm {fun} {a} {b})")
            }
        }
    }
}

impl<U: SmtParam> SmtFormula<U> {
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
            SmtHead::And => Ok(And(args)),
            SmtHead::Or => Ok(Or(args)),
            SmtHead::Eq => Ok(Eq(args)),
            SmtHead::Neq => Ok(Neq(args)),
            SmtHead::Not => {
                let [arg] = args.try_into()?;
                Ok(Not(Box::new(arg)))
            }
            SmtHead::Implies => {
                let [premise, conclusion] = args.try_into()?;
                Ok(Implies(Box::new(premise), Box::new(conclusion)))
            }
            SmtHead::If => {
                let [c, l, r] = args.try_into()?;
                Ok(Ite(Box::new(c), Box::new(l), Box::new(r)))
            }
        }
    }

    /// Optimises the SMT formula in-place.
    fn optimise_mut(&mut self)
    where
        U::SVar: Eq,
    {
        match self {
            SmtFormula::Fun(_, args) | SmtFormula::Eq(args) | SmtFormula::Neq(args) => {
                args.iter_mut().for_each(Self::optimise_mut);
            }
            // smt-lib assumes non-empty sorts (sec 5.3 def 6)
            // This remove
            SmtFormula::Forall(vars, f) | SmtFormula::Exists(vars, f) => {
                f.optimise_mut();
                if vars.is_empty()
                    || f.as_ref()
                        .free_vars_iter()
                        .all(|v| !vars.iter().contains(&v))
                {
                    // gymnastic to set `self` to `f`
                    *self = ::std::mem::take(f.as_mut())
                }
            }
            SmtFormula::And(args) => {
                let args_c = ::std::mem::replace(args, Vec::with_capacity(args.len()));

                for mut arg in args_c {
                    arg.optimise_mut();
                    if arg.is_false() {
                        *self = Self::False;
                        return;
                    } else if arg.is_true() {
                        continue;
                    }
                    args.push(arg);
                }

                if args.is_empty() {
                    *self = Self::True;
                } else if args.len() == 1 {
                    *self = args.pop().unwrap()
                }
            }
            SmtFormula::Or(args) => {
                let args_c = ::std::mem::replace(args, Vec::with_capacity(args.len()));

                for mut arg in args_c {
                    arg.optimise_mut();
                    if arg.is_true() {
                        *self = Self::True;
                        return;
                    } else if arg.is_false() {
                        continue;
                    }
                    args.push(arg);
                }

                if args.is_empty() {
                    *self = Self::False;
                } else if args.len() == 1 {
                    *self = args.pop().unwrap()
                }
            }
            SmtFormula::Implies(a, b) => {
                a.optimise_mut();
                if a.is_false() {
                    *self = Self::True;
                    return;
                }
                b.optimise_mut();
                if a.is_true() || b.is_true() {
                    *self = ::std::mem::take(b.as_mut());
                }
            }
            SmtFormula::Ite(c, l, r) => {
                c.optimise_mut();
                l.optimise_mut();
                r.optimise_mut();
                if c.is_true() {
                    *self = ::std::mem::take(l.as_mut());
                } else if c.is_false() {
                    *self = ::std::mem::take(r.as_mut());
                }
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

    /// Converts a generic formula into an SMT formula.
    pub fn from_formula<V>(f: V) -> Self
    where
        V: IntoSmt<U>,
    {
        let Destructed { head, args } = f.destruct();
        let args = args.map(Self::from_formula);
        match head {
            HeadSk::Var(v) => Self::Var(V::convert_var(v)),
            HeadSk::Fun(fun) => match V::as_head(&fun) {
                Some(head) => match head {
                    SmtHead::True => Self::True,
                    SmtHead::False => Self::False,
                    SmtHead::And => Self::And(args.collect()),
                    SmtHead::Or => Self::Or(args.collect()),
                    SmtHead::Eq => Self::Eq(args.collect()),
                    SmtHead::Neq => Self::Neq(args.collect()),
                    SmtHead::Not => {
                        let mut args = args;
                        let a = args.next().unwrap();
                        debug_assert!(args.next().is_none());
                        Self::Not(Box::new(a))
                    }
                    SmtHead::Implies => {
                        let (a, b) = args.collect_tuple().unwrap();
                        Self::Implies(Box::new(a), Box::new(b))
                    }
                    SmtHead::If => {
                        let (a, b, c) = args.collect_tuple().unwrap();
                        Self::Ite(Box::new(a), Box::new(b), Box::new(c))
                    }
                },
                None => Self::Fun(V::convert_function(fun), args.collect()),
            },
            HeadSk::Quant(binder) => {
                let mut args = args;
                let inner = args.next().unwrap();
                debug_assert!(args.next().is_none());
                match V::convert_quant(binder) {
                    SmtQuantifier::Exists(vars) => Self::Exists(vars, Box::new(inner)),
                    SmtQuantifier::Forall(vars) => Self::Forall(vars, Box::new(inner)),
                }
            }
        }
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
}

/// A trait for types that can be converted into an SMT formula.
pub trait IntoSmt<U: SmtParam>: AsFormula {
    /// Converts a generic function into an SMT function.
    fn convert_function(fun: Self::Fun) -> U::Function;
    /// Converts a generic variable into an SMT sorted variable.
    fn convert_var(var: Self::Var) -> <U as SmtParam>::SVar;
    /// Converts a generic quantifier into an SMT quantifier.
    fn convert_quant(quant: Self::Quant) -> SmtQuantifier<U>;
    /// Converts a generic function head into an SMT head, if applicable.
    fn as_head(fun: &Self::Fun) -> Option<SmtHead>;

    /// Converts the formula into an SMT formula.
    fn into_smt(self) -> SmtFormula<U> {
        SmtFormula::from_formula(self)
    }
}

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

impl<U: SmtParam> AsFormula for SmtFormula<U> {
    /// The variable type for the formula.
    type Var = U::SVar;

    /// The function type for the formula.
    type Fun = SmtFunctions<U::Function>;

    /// The quantifier type for the formula.
    type Quant = SmtQuantifier<U>;

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
                args: MIter::Map(args.into_iter()),
            },
            SmtFormula::Forall(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifier::Forall(vars)),
                args: MIter::One([*f].into_iter()),
            },
            SmtFormula::Exists(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifier::Exists(vars)),
                args: MIter::One([*f].into_iter()),
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
                args: MIter::Map(args.into_iter()),
            },
            SmtFormula::Or(args) => Destructed {
                head: mk(Or),
                args: MIter::Map(args.into_iter()),
            },
            SmtFormula::Eq(args) => Destructed {
                head: mk(Eq),
                args: MIter::Map(args.into_iter()),
            },
            SmtFormula::Neq(args) => Destructed {
                head: mk(Neq),
                args: MIter::Map(args.into_iter()),
            },
            SmtFormula::Not(arg) => Destructed {
                head: mk(Not),
                args: MIter::One([*arg].into_iter()),
            },
            SmtFormula::Implies(a, b) => Destructed {
                head: mk(Implies),
                args: MIter::Map(vec![*a, *b].into_iter()),
            },
            SmtFormula::Ite(c, l, r) => Destructed {
                head: mk(If),
                args: MIter::Map(vec![*c, *l, *r].into_iter()),
            },
            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(_, smt_formula, smt_formula1) => unimplemented!(),
        }
    }
}

impl<'a, U: SmtParam> AsFormula for &'a SmtFormula<U> {
    /// The variable type for the formula.
    type Var = &'a U::SVar;

    /// The function type for the formula.
    type Fun = SmtFunctions<&'a U::Function>;

    /// The quantifier type for the formula.
    type Quant = SmtQuantifierRef<'a, U>;

    /// Destructures the SMT formula into its head and arguments.
    fn destruct(self) -> Destructed<Self, impl Iterator<Item = Self>> {
        dynamic_iter!(MIter; None:A, One:B, Ref:D,Owned:C);

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
                head: HeadSk::Quant(SmtQuantifierRef::Forall(&vars)),
                args: MIter::One([f.as_ref()].into_iter()),
            },
            SmtFormula::Exists(vars, f) => Destructed {
                head: HeadSk::Quant(SmtQuantifierRef::Exists(&vars)),
                args: MIter::One([f.as_ref()].into_iter()),
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
                args: MIter::One([arg.as_ref()].into_iter()),
            },
            SmtFormula::Implies(a, b) => Destructed {
                head: mk(Implies),
                args: MIter::Owned(vec![a.as_ref(), b.as_ref()].into_iter()),
            },
            SmtFormula::Ite(c, l, r) => Destructed {
                head: mk(If),
                args: MIter::Owned(vec![c.as_ref(), l.as_ref(), r.as_ref()].into_iter()),
            },
            #[cfg(feature = "cryptovampire")]
            SmtFormula::Subterm(_, smt_formula, smt_formula1) => unimplemented!(),
        }
    }
}

impl<U: SmtParam> Not for SmtFormula<U> {
    /// The output type of the negation operation.
    type Output = Self;

    /// Applies logical negation to the SMT formula.
    fn not(self) -> Self::Output {
        Self::Not(Box::new(self))
    }
}

impl<U: SmtParam> BitAnd for SmtFormula<U> {
    /// The output type of the bitwise AND operation.
    type Output = Self;

    /// Applies logical AND to two SMT formulas.
    fn bitand(self, rhs: Self) -> Self::Output {
        Self::And(vec![self, rhs])
    }
}

impl<U: SmtParam> BitOr for SmtFormula<U> {
    /// The output type of the bitwise OR operation.
    type Output = Self;

    /// Applies logical OR to two SMT formulas.
    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Or(vec![self, rhs])
    }
}

impl<U: SmtParam> Shr for SmtFormula<U> {
    /// The output type of the right shift operation (used for implication).
    type Output = Self;

    /// Applies logical implication to two SMT formulas.
    fn shr(self, rhs: Self) -> Self::Output {
        Self::Implies(Box::new(self), Box::new(rhs))
    }
}

impl<'a, U: SmtParam> Bounder<&'a U::SVar> for SmtQuantifierRef<'a, U> {
    /// Returns an iterator over the bound variables of the quantifier.
    fn bounds(&self) -> impl Iterator<Item = &'a U::SVar> {
        match self {
            SmtQuantifierRef::Forall(vars) | SmtQuantifierRef::Exists(vars) => vars.iter(),
        }
    }
}
