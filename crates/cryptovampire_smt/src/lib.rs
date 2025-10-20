use std::borrow::Cow;
use std::fmt::{self, Debug, Display};
use std::hash::Hash;

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
    fn mk(sort: Self::Sort) -> Self where Self::Sort: Sized;
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

// pub use var::{VarInner, uvar};
// mod var {
//     use core::fmt;
//     use std::borrow::Cow;
//     use std::fmt::Display;

//     #[allow(non_camel_case_types)]
//     pub type uvar = u32;

//     #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
//     pub enum VarInner {
//         Int(uvar),
//         Str(Cow<'static, str>),
//     }

//     #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
//     pub struct SortedVar<S> {
//         pub var: VarInner,
//         pub sort: S,
//     }

//     impl Display for VarInner {
//         fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//             match self {
//                 VarInner::Int(u) => write!(f, "x_{u:}"),
//                 VarInner::Str(str) => write!(f, "{str}"),
//             }
//         }
//     }

//     impl<S: Display> Display for SortedVar<S> {
//         fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//             let Self { var, sort } = self;
//             write!(f, "({var} {sort})")
//         }
//     }

//     impl<S> SortedVar<S> {
//         pub fn new(i: uvar, sort: S) -> Self {
//             Self {
//                 var: VarInner::Int(i),
//                 sort,
//             }
//         }
//     }
// }

pub(crate) use arr::Arr;
mod arr {
    use core::fmt;
    use std::fmt::Display;

    pub struct Arr<A, B>(pub A, pub B);

    impl<B> Arr<(), B> {
        pub fn simple(b: B) -> Self {
            Arr((), b)
        }
    }

    impl<B> Display for Arr<&str, &[B]>
    where
        B: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Self(header, arr) = self;
            write!(f, "({header}")?;
            for x in *arr {
                write!(f, " {x}")?;
            }
            write!(f, ")")
        }
    }

    impl<B> Display for Arr<(), &[B]>
    where
        B: Display,
    {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            Arr("", self.1).fmt(f)
        }
    }
}

#[non_exhaustive]
#[derive(Debug, Clone, Copy, Default)]
pub struct EvalParam {
    /// Can we simplify the quantifier. In other words are the considered sorts non-empty?
    pub simplify_quantifiers: bool,
}
