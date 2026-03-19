use std::borrow::Cow;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use bitflags::bitflags;
use thiserror::Error;
use utils::implvec;

/// The file extension for SMT files.
pub const SMT_FILE_EXTENSION: &str = ".smt";

#[cfg(feature = "macro")]
/// A macro for generating SMT formulas.
#[allow(unused)]
macro_rules! smt {
    ($($t:tt)*) => {
        cryptovampire_macro::smt!($($t)*)
    };
}

pub use formula::*;
mod formula;

pub use smt::*;
mod smt;

pub mod solvers;

mod formatter;
pub use formatter::Term as SmtPrettyPrinter;
pub(crate) use formatter::translate_smt_to_term;
use utils::reservable::Reservable;

use crate::solvers::{Solver, SolverFeatures};

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct SolverKind : u8 {
        const AssertGround = 1 << 0;
        const AssertTh = 1 << 1;
        const AssertNot = 1 << 2;
        const VampireBuiltins = 1 << 3;
        const Z3Builtins = 1 << 4;
        const CVC5Builtins = 1 << 5;
        const CVSubterm = 1 << 6;
        const CVRewrite = 1 << 7;
    }
}

pub static SMT_COMPLIANT: SolverKind = SolverKind::empty();
pub static VAMPIRE: SolverKind = SolverKind::from_bits(
    SolverKind::AssertGround.bits()
        | SolverKind::AssertTh.bits()
        | SolverKind::AssertNot.bits()
        | SolverKind::VampireBuiltins.bits(),
)
.unwrap();
pub static Z3: SolverKind =
    SolverKind::from_bits(SolverKind::AssertNot.bits() | SolverKind::Z3Builtins.bits()).unwrap();
pub static CVC5: SolverKind =
    SolverKind::from_bits(SMT_COMPLIANT.bits() | SolverKind::CVC5Builtins.bits()).unwrap();

/// A trait for defining parameters used in SMT formulas.
pub trait SmtParam {
    /// The type representing functions in the SMT formula.
    type Function: Display;
    /// The type representing sorts in the SMT formula.
    type Sort: Display + Clone;
    /// The type representing sorted variables in the SMT formula.
    type SVar: SortedVar<Sort = Self::Sort> + Display;
}

/// A trait for variables that have an associated sort.
pub trait SortedVar {
    /// The type representing the sort of the variable.
    type Sort: Display + Clone;

    /// Returns a reference to the sort of the variable.
    fn sort_ref(&self) -> Cow<'_, Self::Sort>;
    /// Creates a new sorted variable with the given sort.
    fn mk(sort: Self::Sort) -> Self
    where
        Self::Sort: Sized;
}

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
/// Represents an SMT file containing a sequence of SMT commands.
pub struct SmtFile<U: SmtParam> {
    /// The content of the SMT file, as a vector of SMT commands.
    pub content: Vec<smt::Smt<U>>,
}

impl<U: SmtParam> PartialEq for SmtFile<U>
where
    smt::Smt<U>: PartialEq,
{
    /// Compares two `SmtFile` instances for equality.
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content
    }
}

impl<U: SmtParam> Eq for SmtFile<U> where smt::Smt<U>: Eq {}

impl<U: SmtParam> PartialOrd for SmtFile<U>
where
    smt::Smt<U>: PartialOrd,
{
    /// Compares two `SmtFile` instances for partial order.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.content.partial_cmp(&other.content)
    }
}

impl<U: SmtParam> Ord for SmtFile<U>
where
    smt::Smt<U>: Ord,
{
    /// Compares two `SmtFile` instances for total order.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.content.cmp(&other.content)
    }
}

impl<U: SmtParam> Hash for SmtFile<U>
where
    smt::Smt<U>: Hash,
{
    /// Hashes the `SmtFile` instance.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.content.hash(state);
    }
}
impl<U: SmtParam> Debug for SmtFile<U>
where
    smt::Smt<U>: Debug,
{
    /// Formats the `SmtFile` for debugging.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtFile")
            .field("content", &self.content)
            .finish()
    }
}

impl<U: SmtParam> Clone for SmtFile<U>
where
    smt::Smt<U>: Clone,
{
    /// Clones the `SmtFile` instance.
    fn clone(&self) -> Self {
        Self {
            content: self.content.clone(),
        }
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, Default)]
pub struct EvalParam {
    /// Can we simplify the quantifier. In other words are the considered sorts non-empty?
    pub simplify_quantifiers: bool,
}

/// Writes a parenthesized expression to the formatter.
#[inline]
fn write_par(
    fmt: &mut std::fmt::Formatter<'_>,
    f: impl FnOnce(&mut std::fmt::Formatter<'_>) -> std::fmt::Result,
) -> std::fmt::Result {
    write!(fmt, "(")?;
    f(fmt)?;
    write!(fmt, ") ")
}

/// Writes a list of items to the formatter, enclosed in parentheses.
#[inline]
fn write_list<A>(
    iter: implvec!(A),
    f: &mut std::fmt::Formatter<'_>,
    mut arg: impl FnMut(&mut std::fmt::Formatter<'_>, A) -> std::fmt::Result,
) -> std::fmt::Result {
    write_par(f, |f| iter.into_iter().try_for_each(|x| arg(f, x)))
}

impl SolverKind {
    pub fn iter_solvers(self) -> impl Iterator<Item = Self> {
        self.iter().filter(|&f| {
            f == Self::empty()
                || f == Self::VampireBuiltins
                || f == Self::Z3Builtins
                || f == Self::CVC5Builtins
        })
    }

    pub const fn builtins_to_solvers(self) -> Option<Solver> {
        if self.is_empty() {
            return Some(Solver::Generic);
        }
        match self {
            SolverKind::VampireBuiltins => Some(Solver::Vampire),
            SolverKind::Z3Builtins => Some(Solver::Z3),
            SolverKind::CVC5Builtins => Some(Solver::Cvc5),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Error)]
pub enum CheckError {
    #[error("'{fun}' clashses with a builtin keyword/function/sort for {solver}.")]
    BuiltinNameClash {
        fun: Box<str>,
        solver: solvers::Solver,
    },
    #[error("the targeted solver doesn't support {0}")]
    UnsupportedFeature(SolverFeatures),

    #[error("empty quantifier")]
    EmptyQuantifier,
}

pub trait SmtSink<U: SmtParam>
where
    <U as SmtParam>::SVar: std::cmp::Eq,
{
    fn extend_smt(&mut self, iter: implvec!(Smt<U>));
    fn reserve(&mut self, size: usize);

    fn extend_one_smt(&mut self, smt: Smt<U>) {
        self.extend_smt(Some(smt));
    }

    fn assert_many(&mut self, iter: implvec!(SmtFormula<U>)) {
        self.extend_smt(iter.into_iter().map(Smt::mk_assert));
    }

    fn assert_one(&mut self, formula: SmtFormula<U>) {
        self.assert_many(Some(formula));
    }

    fn comment(&mut self, comment: impl Display) {
        self.extend_one_smt(Smt::Comment(comment.to_string()));
    }

    fn comment_block(&mut self, comment: impl Display) {
        self.extend_one_smt(Smt::comment_block(comment.to_string()));
    }
}

impl<U, V> SmtSink<U> for V
where
    U: SmtParam,
    V: Extend<Smt<U>> + Reservable,
    <U as SmtParam>::SVar: std::cmp::Eq,
{
    fn extend_smt(&mut self, iter: implvec!(Smt<U>)) {
        self.extend(iter);
    }

    fn reserve(&mut self, size: usize) {
        self.gen_reserve(size);
    }
}
