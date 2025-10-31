use std::borrow::Cow;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

use utils::implvec;

pub const SMT_FILE_EXTENSION: &str = ".smt";

#[cfg(feature = "macro")]
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

pub trait SmtParam {
    type Function: Display;
    type Sort: Display + Clone;
    type SVar: SortedVar<Sort = Self::Sort> + Display;
}

pub trait SortedVar {
    type Sort: Display + Clone;

    fn sort_ref(&self) -> Cow<'_, Self::Sort>;
    fn mk(sort: Self::Sort) -> Self
    where
        Self::Sort: Sized;
}

// #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtFile<U: SmtParam> {
    pub content: Vec<smt::Smt<U>>,
}

impl<U: SmtParam> PartialEq for SmtFile<U>
where
    smt::Smt<U>: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content
    }
}

impl<U: SmtParam> Eq for SmtFile<U> where smt::Smt<U>: Eq {}

impl<U: SmtParam> PartialOrd for SmtFile<U>
where
    smt::Smt<U>: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.content.partial_cmp(&other.content)
    }
}

impl<U: SmtParam> Ord for SmtFile<U>
where
    smt::Smt<U>: Ord,
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.content.cmp(&other.content)
    }
}

impl<U: SmtParam> Hash for SmtFile<U>
where
    smt::Smt<U>: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.content.hash(state);
    }
}
impl<U: SmtParam> Debug for SmtFile<U>
where
    smt::Smt<U>: Debug,
{
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
