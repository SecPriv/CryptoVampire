use std::fmt::Display;

use itertools::izip;
use utils::implvec;

use crate::Arr;

use super::SmtFile;

use super::SortedVar;

use super::formula::SmtFormula;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt<S, F> {
    Assert(SmtFormula<S, F>),
    #[cfg(feature = "vampire")]
    AssertTh(SmtFormula<S, F>),
    #[cfg(feature = "cryptovampire")]
    AssertGround {
        sort: S,
        formula: SmtFormula<S, F>,
    },
    #[cfg(feature = "vampire")]
    AssertNot(SmtFormula<S, F>),
    DeclareFun {
        fun: F,
        args: Vec<S>,
        out: S,
    },
    DeclareSort(S),
    DeclareSortAlias {
        from: S,
        to: S,
    },

    #[cfg(feature = "cryptovampire")]
    DeclareSubtermRelation(F, Vec<F>),

    #[cfg(feature = "cryptovampire")]
    DeclareRewrite {
        rewrite_fun: RewriteKind<F>,
        vars: Vec<SortedVar<S>>,
        lhs: Box<SmtFormula<S, F>>,
        rhs: Box<SmtFormula<S, F>>,
    },

    DeclareDatatypes {
        sorts: Vec<S>,
        cons: Vec<Vec<SmtCons<S, F>>>,
    },
    Comment(String),

    CheckSat,
    GetProof,
    SetOption(String, String),
    SetLogic(String),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtCons<S, F> {
    pub fun: F,
    pub sorts: Vec<S>,
    pub dest: Vec<F>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg(feature = "cryptovampire")]
pub enum RewriteKind<F> {
    Bool,
    Other(F),
}

impl<S, F> FromIterator<Smt<S, F>> for SmtFile<S, F> {
    fn from_iter<T: IntoIterator<Item = Smt<S, F>>>(iter: T) -> Self {
        SmtFile {
            content: iter.into_iter().collect(),
        }
    }
}

impl<S, F> Smt<S, F> {
    /// Returns `true` if the smt is [`Assert`].
    ///
    /// [`Assert`]: Smt::Assert
    #[must_use]
    pub fn is_any_assert(&self) -> bool {
        matches!(
            self,
            Self::Assert(..) | Self::AssertNot(..) | Self::AssertTh(..)
        )
    }
}

impl<S, F> Smt<S, F> where SmtFormula<S, F>:Eq {
    pub fn mk_assert(f:SmtFormula<S, F>) -> Self {
        Self::Assert(f.optimise())
    }
}

#[inline]
fn write_par(
    fmt: &mut std::fmt::Formatter<'_>,
    f: impl FnOnce(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
) -> std::fmt::Result {
    write!(fmt, "(")?;
    f(fmt)?;
    write!(fmt, ") ")
}

#[inline]
fn write_list<A>(
    iter: implvec!(A),
    f: &mut std::fmt::Formatter<'_>,
    mut arg: impl FnMut(&mut std::fmt::Formatter<'_>, A) -> std::fmt::Result,
) -> std::fmt::Result {
    write_par(f, |f| iter.into_iter().try_for_each(|x| arg(f, x)))
}

impl<S, F> Display for Smt<S, F>
where
    S: Display,
    F: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Smt::Assert(formula) => writeln!(f, "(assert {formula})"),
            #[cfg(feature = "vampire")]
            Smt::AssertTh(formula) => writeln!(f, "(assert-theory {formula})"),
            #[cfg(feature = "cryptovampire")]
            Smt::AssertGround { sort, formula } => writeln!(f, "(assert-ground {sort} {formula})"),
            #[cfg(feature = "vampire")]
            Smt::AssertNot(formula) => writeln!(f, "(assert-not {formula})"),
            Smt::DeclareFun { fun, args, out } => writeln!(
                f,
                "(declare-fun {fun} ({}) {out})",
                Arr::simple(args.as_slice())
            ),
            Smt::DeclareSort(s) => writeln!(f, "(declare-sort {s})"),
            Smt::DeclareSortAlias { from, to } => writeln!(f, "(define-sort {from} () {to})"),
            #[cfg(feature = "cryptovampire")]
            Smt::DeclareSubtermRelation(fun, funs) => {
                write!(f, "(declare-subterm-relation {fun} ")?;
                for fun in funs {
                    write!(f, " {fun}")?;
                }
                writeln!(f, ")")
            }
            #[cfg(feature = "cryptovampire")]
            Smt::DeclareRewrite {
                rewrite_fun,
                vars,
                lhs,
                rhs,
            } => {
                write!(f, "(declare-rewrite ")?;
                {
                    write!(f, "(forall {} (", Arr::simple(vars.as_slice()))?;
                    match rewrite_fun {
                        RewriteKind::Bool => write!(f, "="),
                        RewriteKind::Other(fun) => write!(f, "{fun}"),
                    }?;
                    write!(f, " {lhs} {rhs})")?;
                }
                writeln!(f, ")")
            }
            Smt::DeclareDatatypes { sorts, cons } => write_par(f, |f| {
                write!(f, "declare-datatypes")?;

                write_list(sorts, f, |f, s| write!(f, "({s} 0)"))?;

                write_list(cons, f, |f, cons| {
                    write_list(cons, f, |f, SmtCons { fun, sorts, dest }| {
                        write!(f, "{fun} ")?;
                        write_list(izip!(sorts, dest), f, |f, (s, dest)| {
                            write!(f, "({dest} {s}) ")
                        })
                    })
                })
            }),
            Smt::Comment(c) => writeln!(f, "; {c}"),
            Smt::CheckSat => writeln!(f, "(check-sat)"),
            Smt::GetProof => writeln!(f, "(get-proof)"),
            Smt::SetOption(option, arg) => writeln!(f, "(set-option :{} {})", option, arg),
            Smt::SetLogic(logic) => writeln!(f, "(set-logic {logic})"),
        }
    }
}
