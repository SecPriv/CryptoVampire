use std::borrow::Cow;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use utils::implvec;

/// The file extension for SMT files.
pub const SMT_FILE_EXTENSION: &str = ".smt";

#[cfg(feature = "macro")]
/// A macro for generating SMT formulas.
macro_rules! smt {
    ($($t:tt)*) => {
        cryptovampire_macro::smt!($($t)*)
    };
}

pub use formula::*;
mod formula;

pub use smt::*;
mod smt;

mod formatter;
pub use formatter::Term as SmtPrettyPrinter;
pub(crate) use formatter::translate_smt_to_term;

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
