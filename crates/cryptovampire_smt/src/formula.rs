use std::borrow::Cow;
use std::fmt::Display;
use std::ops::{BitAnd, BitOr, Not, Shr};

use itertools::Itertools;
use logic_formula::{Bounder, Destructed, Formula, HeadSk};
use utils::{dynamic_iter, ereturn_if, implvec};

use super::SortedVar;
use crate::{Arr, EvalParam, SmtParam};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<U: SmtParam> {
    Var(U::SVar),
    Fun(U::Function, Vec<SmtFormula<U>>),
    Forall(Vec<U::SVar>, Box<SmtFormula<U>>),
    Exists(Vec<U::SVar>, Box<SmtFormula<U>>),

    True,
    False,
    And(Vec<SmtFormula<U>>),
    Or(Vec<SmtFormula<U>>),
    Eq(Vec<SmtFormula<U>>),
    Neq(Vec<SmtFormula<U>>),
    Not(Box<SmtFormula<U>>),
    Implies(Box<SmtFormula<U>>, Box<SmtFormula<U>>),

    Ite(Box<SmtFormula<U>>, Box<SmtFormula<U>>, Box<SmtFormula<U>>),

    #[cfg(feature = "cryptovampire")]
    Subterm(U::Function, Box<SmtFormula<U>>, Box<SmtFormula<U>>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtHead {
    True,
    False,
    And,
    Or,
    Eq,
    Neq,
    Not,
    Implies,
    If,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum SmtQuantifier<U: SmtParam> {
    Forall(Vec<U::SVar>),
    Exists(Vec<U::SVar>),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SmtQuantifierRef<'a, U: SmtParam> {
    Forall(&'a [U::SVar]),
    Exists(&'a [U::SVar]),
}

impl<U: SmtParam> Default for SmtFormula<U> {
    fn default() -> Self {
        Self::True
    }
}

impl<U> Display for SmtFormula<U>
where
    U: SmtParam,
{
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
            SmtFormula::Forall(vars, formula) => {
                write!(f, "(forall {} {formula})", Arr::simple(vars.as_slice()))
            }
            SmtFormula::Exists(vars, formula) => {
                write!(f, "(exists {} {formula})", Arr::simple(vars.as_slice()))
            }
            SmtFormula::True => write!(f, "true"),
            SmtFormula::False => write!(f, "false"),
            SmtFormula::And(args) => Arr("and", args.as_slice()).fmt(f),
            SmtFormula::Or(args) => Arr("or", args.as_slice()).fmt(f),
            SmtFormula::Eq(args) => Arr("=", args.as_slice()).fmt(f),
            SmtFormula::Neq(args) => Arr("distinct", args.as_slice()).fmt(f),
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

    pub fn optimise(mut self) -> Self
    where
        U::SVar: Eq,
    {
        self.optimise_mut();
        self
    }

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

pub trait IntoSmt<U: SmtParam>: Formula {
    fn convert_function(fun: Self::Fun) -> U::Function;
    fn convert_var(var: Self::Var) -> <U as SmtParam>::SVar;
    fn convert_quant(quant: Self::Quant) -> SmtQuantifier<U>;
    fn as_head(fun: &Self::Fun) -> Option<SmtHead>;

    fn into_smt(self) -> SmtFormula<U> {
        SmtFormula::from_formula(self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtFunctions<F> {
    Smt(SmtHead),
    Fun(F),
}

impl<F> From<F> for SmtFunctions<F> {
    fn from(v: F) -> Self {
        Self::Fun(v)
    }
}

impl<U: SmtParam> Formula for SmtFormula<U> {
    type Var = U::SVar;

    type Fun = SmtFunctions<U::Function>;

    type Quant = SmtQuantifier<U>;

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

impl<'a, U: SmtParam> Formula for &'a SmtFormula<U> {
    type Var = &'a U::SVar;

    type Fun = SmtFunctions<&'a U::Function>;

    type Quant = SmtQuantifierRef<'a, U>;

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
    type Output = Self;

    fn not(self) -> Self::Output {
        Self::Not(Box::new(self))
    }
}

impl<U: SmtParam> BitAnd for SmtFormula<U> {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Self::And(vec![self, rhs])
    }
}

impl<U: SmtParam> BitOr for SmtFormula<U> {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Self::Or(vec![self, rhs])
    }
}

impl<U: SmtParam> Shr for SmtFormula<U> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        Self::Implies(Box::new(self), Box::new(rhs))
    }
}

impl<'a, U: SmtParam> Bounder<&'a U::SVar> for SmtQuantifierRef<'a, U> {
    fn bounds(&self) -> impl Iterator<Item = &'a U::SVar> {
        match self {
            SmtQuantifierRef::Forall(vars) | SmtQuantifierRef::Exists(vars) => vars.iter(),
        }
    }
}
