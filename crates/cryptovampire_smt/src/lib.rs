use std::{
    borrow::Cow,
    fmt::{self, Display},
};

pub const SMT_FILE_EXTENSION: &str = ".smt";

#[cfg(feature = "macro")]
macro_rules! smt {
    ($($t:tt)*) => {
        cryptovampire_macor::smt!($($t)*)
    };
}

pub use formula::*;
mod formula;

pub use smt::*;
mod smt;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtFile<S, F> {
    pub content: Vec<smt::Smt<S, F>>,
}

pub use var::{SortedVar, VarInner, uvar};
mod var {
    use core::fmt;
    use std::{borrow::Cow, fmt::Display};

    #[allow(non_camel_case_types)]
    pub type uvar = u32;

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    pub enum VarInner {
        Int(uvar),
        Str(Cow<'static, str>),
    }

    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
    pub struct SortedVar<S> {
        pub var: VarInner,
        pub sort: S,
    }

    impl Display for VarInner {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                VarInner::Int(u) => write!(f, "x_{u:}"),
                VarInner::Str(str) => write!(f, "{str}"),
            }
        }
    }

    impl<S: Display> Display for SortedVar<S> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Self { var, sort } = self;
            write!(f, "({var} {sort})")
        }
    }

    impl<S> SortedVar<S> {
        pub fn new(i: uvar, sort: S) -> Self {
            Self {
                var: VarInner::Int(i),
                sort,
            }
        }
    }
}

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
