use std::convert::identity;
use std::fmt::Display;

use itertools::izip;
use quarck::CowArc;
use static_init::dynamic;

use super::formula::SmtFormula;
use super::{SmtFile, SortedVar};
use crate::solvers::{Solver, SolverFeatures};
use crate::{
    CheckError, SmtParam, SmtPrettyPrinter, SolverKind, translate_smt_to_term, write_list,
    write_par,
};

/// Represents an SMT-LIB command.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Smt<'a, U: SmtParam> {
    /// An `assert` command.
    Assert(SmtFormula<'a, U>),
    #[cfg(feature = "vampire")]
    /// An `assert-theory` command (Vampire specific).
    AssertTh(SmtFormula<'a, U>),
    #[cfg(feature = "cryptovampire")]
    /// An `assert-ground` command (Cryptovampire specific).
    AssertGround {
        sort: U::Sort,
        formula: SmtFormula<'a, U>,
    },
    #[cfg(feature = "vampire")]
    /// An `assert-not` command (Vampire specific).
    AssertNot(SmtFormula<'a, U>),
    /// A `declare-fun` command.
    DeclareFun {
        fun: U::Function,
        args: CowArc<'a, [U::Sort]>,
        out: U::Sort,
    },
    /// A `declare-sort` command.
    DeclareSort(U::Sort),
    /// A `define-sort` command (alias).
    DeclareSortAlias { from: U::Sort, to: U::Sort },

    #[cfg(feature = "cryptovampire")]
    /// A `declare-subterm-relation` command (Cryptovampire specific).
    DeclareSubtermRelation(U::Function, CowArc<'a, [U::Function]>),

    #[cfg(feature = "cryptovampire")]
    /// A `declare-rewrite` command (Cryptovampire specific).
    DeclareRewrite {
        rewrite_fun: RewriteKind<U::Function>,
        vars: Vec<U::SVar>,
        lhs: Box<SmtFormula<'a, U>>,
        rhs: Box<SmtFormula<'a, U>>,
    },

    /// A `declare-datatypes` command.
    DeclareDatatypes {
        sorts: Vec<<U::SVar as SortedVar>::Sort>,
        cons: Vec<Vec<SmtCons<U>>>,
    },
    /// A comment.
    Comment(String),

    /// A `check-sat` command.
    CheckSat,
    /// A `get-proof` command.
    GetProof,
    /// A `set-option` command.
    SetOption(String, String),
    /// A `set-logic` command.
    SetLogic(String),
}

impl<'a, U: SmtParam> Smt<'a, U> {
    /// Converts the SMT command into a pretty-printable `SmtPrettyPrinter` term.
    pub fn as_pretty(&self) -> SmtPrettyPrinter {
        translate_smt_to_term(self)
    }
}

impl<'a, U: SmtParam> Clone for Smt<'a, U> {
    fn clone(&self) -> Self {
        match self {
            Self::Assert(arg0) => Self::Assert(arg0.clone()),
            #[cfg(feature = "vampire")]
            Self::AssertTh(arg0) => Self::AssertTh(arg0.clone()),
            #[cfg(feature = "cryptovampire")]
            Self::AssertGround { sort, formula } => Self::AssertGround {
                sort: sort.clone(),
                formula: formula.clone(),
            },
            #[cfg(feature = "vampire")]
            Self::AssertNot(arg0) => Self::AssertNot(arg0.clone()),
            Self::DeclareFun { fun, args, out } => Self::DeclareFun {
                fun: fun.clone(),
                args: args.clone(),
                out: out.clone(),
            },
            Self::DeclareSort(arg0) => Self::DeclareSort(arg0.clone()),
            Self::DeclareSortAlias { from, to } => Self::DeclareSortAlias {
                from: from.clone(),
                to: to.clone(),
            },
            #[cfg(feature = "cryptovampire")]
            Self::DeclareSubtermRelation(arg0, arg1) => {
                Self::DeclareSubtermRelation(arg0.clone(), arg1.clone())
            }
            #[cfg(feature = "cryptovampire")]
            Self::DeclareRewrite {
                rewrite_fun,
                vars,
                lhs,
                rhs,
            } => Self::DeclareRewrite {
                rewrite_fun: rewrite_fun.clone(),
                vars: vars.clone(),
                lhs: lhs.clone(),
                rhs: rhs.clone(),
            },
            Self::DeclareDatatypes { sorts, cons } => Self::DeclareDatatypes {
                sorts: sorts.clone(),
                cons: cons.clone(),
            },
            Self::Comment(arg0) => Self::Comment(arg0.clone()),
            Self::CheckSat => Self::CheckSat,
            Self::GetProof => Self::GetProof,
            Self::SetOption(arg0, arg1) => Self::SetOption(arg0.clone(), arg1.clone()),
            Self::SetLogic(arg0) => Self::SetLogic(arg0.clone()),
        }
    }
}

/// Represents a constructor for a datatype in SMT-LIB.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SmtCons<U: SmtParam> {
    /// The function symbol of the constructor.
    pub fun: U::Function,
    /// The sorts of the arguments to the constructor.
    pub sorts: Vec<U::Sort>,
    /// The destructors for the constructor's arguments.
    pub dest: Vec<Option<U::Function>>,
}

/// Represents the kind of rewrite rule.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg(feature = "cryptovampire")]
pub enum RewriteKind<F> {
    /// A boolean rewrite rule.
    Bool,
    /// Another kind of rewrite rule with a function.
    Other(F),
}

impl<U: SmtParam> Clone for SmtCons<U> {
    fn clone(&self) -> Self {
        Self {
            fun: self.fun.clone(),
            sorts: self.sorts.clone(),
            dest: self.dest.clone(),
        }
    }
}

impl<'a, U: SmtParam> FromIterator<Smt<'a, U>> for SmtFile<'a, U> {
    /// Creates an `SmtFile` from an iterator of `Smt` commands.
    fn from_iter<T: IntoIterator<Item = Smt<'a, U>>>(iter: T) -> Self {
        SmtFile {
            content: iter.into_iter().collect(),
        }
    }
}

impl<'a, U: SmtParam> Smt<'a, U> {
    /// Returns `true` if the smt is [`Assert`].
    ///
    /// [`Assert`]: Smt::Assert
    #[must_use]
    pub fn is_any_assert(&self) -> bool {
        match self {
            Self::Assert(..) => true,
            #[cfg(feature = "vampire")]
            Self::AssertNot(..) | Self::AssertTh(..) => true,
            _ => false,
        }
    }

    /// Creates an SMT query command (asserting the negation of the given formula).
    pub fn mk_query(query: SmtFormula<'a, U>) -> Self
    where
        U::SVar: Eq,
    {
        #[cfg(feature = "vampire")]
        {
            Self::AssertNot(query.optimise())
        }

        #[cfg(not(feature = "vampire"))]
        {
            Self::Assert((!query).optimise())
        }
    }

    /// Creates an SMT comment block from a displayable type.
    pub fn comment_block(str: impl Display) -> Self {
        Self::Comment(make_comment_block(str))
    }
}

impl<'a, U: SmtParam> Smt<'a, U>
where
    U::SVar: Eq,
{
    /// Creates an SMT assert command with an optimised formula.
    pub fn mk_assert(f: SmtFormula<'a, U>) -> Self {
        Self::Assert(f.optimise())
    }

    pub fn check(&self, kind: SolverKind) -> Result<(), CheckError> {
        match self {
            Self::Comment(_)
            | Self::CheckSat
            | Self::GetProof
            | Self::SetOption(_, _)
            | Self::SetLogic(_) => Ok(()),

            // Asserts
            #[cfg(feature = "vampire")]
            Self::AssertTh(f) => {
                if kind.contains(SolverKind::AssertTh) {
                    f.check(kind)
                } else {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::AssertTh))
                }
            }
            #[cfg(feature = "cryptovampire")]
            Self::AssertGround { formula, .. } => {
                if kind.contains(SolverKind::AssertGround) {
                    formula.check(kind)
                } else {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::AssertGround))
                }
            }
            #[cfg(feature = "vampire")]
            Self::AssertNot(f) => {
                if kind.contains(SolverKind::AssertGround) {
                    f.check(kind)
                } else {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::AssertNot))
                }
            }
            Self::Assert(f) => f.check(kind),

            // Declarations
            Self::DeclareFun { fun, .. } => Self::check_fun(fun.to_string(), kind),
            #[cfg(feature = "cryptovampire")]
            Self::DeclareSubtermRelation(f, _) => {
                if kind.contains(SolverKind::CVSubterm) {
                    Self::check_fun(f.to_string(), kind)
                } else {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::Subterm))
                }
            }
            Self::DeclareSort(s) | Self::DeclareSortAlias { to: s, .. } => {
                Self::check_fun(s.to_string(), kind)
            }
            #[cfg(feature = "cryptovampire")]
            Self::DeclareRewrite { lhs, rhs, .. } => {
                if kind.contains(SolverKind::CVRewrite) {
                    lhs.check(kind)?;
                    rhs.check(kind)
                } else {
                    Err(CheckError::UnsupportedFeature(SolverFeatures::Rewrite))
                }
            }
            Self::DeclareDatatypes { sorts, cons } => {
                for s in sorts {
                    Self::check_fun(s.to_string(), kind)?
                }
                for SmtCons { fun, dest, .. } in cons.iter().flat_map(|v| v.iter()) {
                    Self::check_fun(fun.to_string(), kind)?;
                    for dest in dest.iter().filter_map(Option::as_ref) {
                        Self::check_fun(dest.to_string(), kind)?
                    }
                }
                Ok(())
            }
        }
    }

    fn check_fun(fun_init: String, kind: SolverKind) -> Result<(), CheckError> {
        let fun = fun_init.trim();
        if Solver::Generic.reserved_keywords().contains(fun) {
            return Err(CheckError::BuiltinNameClash {
                fun: fun_init.into_boxed_str(),
                solver: Solver::Generic,
            });
        }
        for s in kind {
            if let Some(solver) = SolverKind::builtins_to_solvers(s)
                && solver.reserved_keywords().contains(fun)
            {
                return Err(CheckError::BuiltinNameClash {
                    fun: fun_init.into_boxed_str(),
                    solver,
                });
            }
        }
        Ok(())
    }

    pub fn convert<'b>(&'a self, kind: SolverKind) -> Result<Smt<'b, U>, CheckError>
    where
        'a: 'b,
    {
        match self {
            #[cfg(feature = "vampire")]
            Self::AssertTh(f) if !kind.contains(SolverKind::AssertTh) => {
                Ok(Self::Assert(f.clone()))
            }
            #[cfg(feature = "vampire")]
            Self::AssertNot(f) if !kind.contains(SolverKind::AssertGround) => {
                Ok(Self::Assert(SmtFormula::Not(CowArc::Borrowed(f))))
            }

            #[cfg(feature = "cryptovampire")]
            Self::AssertGround { .. } if !kind.contains(SolverKind::AssertGround) => {
                Err(CheckError::UnsupportedFeature(SolverFeatures::AssertGround))
            }
            #[cfg(feature = "cryptovampire")]
            Self::DeclareSubtermRelation(_, _) if !kind.contains(SolverKind::CVSubterm) => {
                Err(CheckError::UnsupportedFeature(SolverFeatures::Subterm))
            }
            #[cfg(feature = "cryptovampire")]
            Self::DeclareRewrite { .. } if !kind.contains(SolverKind::CVRewrite) => {
                Err(CheckError::UnsupportedFeature(SolverFeatures::Rewrite))
            }
            x => Ok(x.clone()),
        }
    }
}

impl<'a, U: SmtParam> Display for Smt<'a, U> {
    /// Formats the SMT command for display in SMT-LIB format.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let p = self.as_pretty();
        write!(f, "{p}")
    }
}

// =========================================================
// ============ text wrapping (from chat gpt) ==============
// =========================================================
/// Creates a formatted comment block string.
fn make_comment_block<T: Display>(input: T) -> String {
    const WIDTH: usize = 80 - 2;
    const BORDER_CHAR: char = '=';

    let text = input.to_string();
    let max_line_length = WIDTH - 2; // at least one '=' on each side

    let wrapped_lines = wrap_text(&text, max_line_length);

    // Format the wrapped lines centered within '=' borders
    let mut result = String::new();
    result.push_str(&BORDER_CHAR.to_string().repeat(WIDTH));
    result.push('\n');
    for line in wrapped_lines {
        let line_length = line.len();
        let total_padding = WIDTH - 2 - line_length;
        let left_padding = total_padding / 2;
        let right_padding = total_padding - left_padding;
        result.push_str(&BORDER_CHAR.to_string().repeat(left_padding));
        result.push(' ');
        result.push_str(&line);
        result.push(' ');
        result.push_str(&BORDER_CHAR.to_string().repeat(right_padding));
        result.push('\n');
    }
    result.push_str(&BORDER_CHAR.to_string().repeat(WIDTH));
    result
}

// Naive word-wrapping: breaks lines at whitespace without splitting words
/// Naively wraps text to a given maximum width.
fn wrap_text(text: &str, max_width: usize) -> Vec<String> {
    let mut lines = Vec::new();
    let mut current_line = String::new();

    for word in text.split_whitespace() {
        if current_line.len() + word.len() + 1 > max_width && !current_line.is_empty() {
            lines.push(current_line.clone());
            current_line.clear();
        }
        if !current_line.is_empty() {
            current_line.push(' ');
        }
        current_line.push_str(word);
    }

    if !current_line.is_empty() {
        lines.push(current_line);
    }

    lines
}

// =========================================================
// =================== pretty printing =====================
// =========================================================
