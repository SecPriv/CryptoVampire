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
    type Function: Display + Clone;
    /// The type representing sorts in the SMT formula.
    type Sort: Display + Clone;
    /// The type representing sorted variables in the SMT formula.
    type SVar: SortedVar<Sort = Self::Sort> + Display + Clone;
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
pub struct SmtFile<'a, U: SmtParam> {
    /// The content of the SMT file, as a vector of SMT commands.
    pub content: Vec<smt::Smt<'a, U>>,
}

impl<'a, U: SmtParam> PartialEq for SmtFile<'a, U>
where
    smt::Smt<'a, U>: PartialEq,
{
    /// Compares two `SmtFile` instances for equality.
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content
    }
}

impl<'a, U: SmtParam> Eq for SmtFile<'a, U> where smt::Smt<'a, U>: Eq {}

impl<'a, U: SmtParam> PartialOrd for SmtFile<'a, U>
where
    smt::Smt<'a, U>: PartialOrd,
{
    /// Compares two `SmtFile` instances for partial order.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.content.partial_cmp(&other.content)
    }
}

impl<'a, U: SmtParam> Ord for SmtFile<'a, U>
where
    smt::Smt<'a, U>: Ord,
{
    /// Compares two `SmtFile` instances for total order.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.content.cmp(&other.content)
    }
}

impl<'a, U: SmtParam> Hash for SmtFile<'a, U>
where
    smt::Smt<'a, U>: Hash,
{
    /// Hashes the `SmtFile` instance.
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.content.hash(state);
    }
}
impl<'a, U: SmtParam> Debug for SmtFile<'a, U>
where
    smt::Smt<'a, U>: Debug,
{
    /// Formats the `SmtFile` for debugging.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtFile")
            .field("content", &self.content)
            .finish()
    }
}

impl<'a, U: SmtParam> Clone for SmtFile<'a, U>
where
    smt::Smt<'a, U>: Clone,
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
