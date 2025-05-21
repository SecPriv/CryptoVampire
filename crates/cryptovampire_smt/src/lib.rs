pub const SMT_FILE_EXTENSION: &str = ".smt";

use std::{
    fmt::{self, Display},
    sync::Arc,
};
// mod display;

use utils::implvec;

// use self::display::{SmtDisplayer, SmtEnv};

pub type uvar = u32;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtFile<S, F> {
    pub content: Vec<Smt<S, F>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct SortedVar<S> {
    pub var: uvar,
    pub sort: S,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum SmtFormula<S, F> {
    Var(u32),
    Fun(F, Vec<SmtFormula<S, F>>),
    Forall(Vec<SortedVar<S>>, Box<SmtFormula<S, F>>),
    Exists(Vec<SortedVar<S>>, Box<SmtFormula<S, F>>),

    True,
    False,
    And(Vec<SmtFormula<S, F>>),
    Or(Vec<SmtFormula<S, F>>),
    Eq(Vec<SmtFormula<S, F>>),
    Neq(Vec<SmtFormula<S, F>>),
    Not(Box<SmtFormula<S, F>>),
    Implies(Box<SmtFormula<S, F>>, Box<SmtFormula<S, F>>),

    Ite(
        Box<SmtFormula<S, F>>,
        Box<SmtFormula<S, F>>,
        Box<SmtFormula<S, F>>,
    ),

    #[cfg(feature = "cryptovampire")]
    Subterm(F, Box<SmtFormula<S, F>>, Box<SmtFormula<S, F>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt<S, F> {
    Assert(SmtFormula<S, F>),
    #[cfg(feature = "cryptovampire")]
    AssertTh(SmtFormula<S, F>),
    #[cfg(feature = "cryptovampire")]
    AssertGround {
        sort: S,
        formula: SmtFormula<S, F>,
    },
    #[cfg(feature = "cryptovampire")]
    AssertNot(SmtFormula<S, F>),
    DeclareFun(F),
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
        cons: Vec<Vec<SmtCons<F>>>,
    },
    Comment(String),

    CheckSat,
    GetProof,
    SetOption(String, String),
    SetLogic(String),
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct SmtCons<F> {
    pub fun: F,
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

impl<S: Display> Display for SortedVar<S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { var, sort } = self;
        write!(f, "(x_{var:} {sort}")
    }
}
