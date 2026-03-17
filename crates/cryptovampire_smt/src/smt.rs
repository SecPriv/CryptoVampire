use std::convert::identity;
use std::fmt::Display;

use itertools::izip;
use static_init::dynamic;

use super::formula::SmtFormula;
use super::{SmtFile, SortedVar};
use crate::solvers::{Solver, SolverFeatures};
use crate::{
    CheckError, SmtParam, SmtPrettyPrinter, SolverKind, translate_smt_to_term, write_list,
    write_par,
};

/// Represents an SMT-LIB command.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum Smt<U: SmtParam> {
    /// An `assert` command.
    Assert(SmtFormula<U>),
    #[cfg(feature = "vampire")]
    /// An `assert-theory` command (Vampire specific).
    AssertTh(SmtFormula<U>),
    #[cfg(feature = "cryptovampire")]
    /// An `assert-ground` command (Cryptovampire specific).
    AssertGround {
        sort: U::Sort,
        formula: SmtFormula<U>,
    },
    #[cfg(feature = "vampire")]
    /// An `assert-not` command (Vampire specific).
    AssertNot(SmtFormula<U>),
    /// A `declare-fun` command.
    DeclareFun {
        fun: U::Function,
        args: Vec<U::Sort>,
        out: U::Sort,
    },
    /// A `declare-sort` command.
    DeclareSort(U::Sort),
    /// A `define-sort` command (alias).
    DeclareSortAlias { from: U::Sort, to: U::Sort },

    #[cfg(feature = "cryptovampire")]
    /// A `declare-subterm-relation` command (Cryptovampire specific).
    DeclareSubtermRelation(U::Function, Vec<U::Function>),

    #[cfg(feature = "cryptovampire")]
    /// A `declare-rewrite` command (Cryptovampire specific).
    DeclareRewrite {
        rewrite_fun: RewriteKind<U::Function>,
        vars: Vec<U::SVar>,
        lhs: Box<SmtFormula<U>>,
        rhs: Box<SmtFormula<U>>,
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

impl<U: SmtParam> Smt<U> {
    /// Converts the SMT command into a pretty-printable `SmtPrettyPrinter` term.
    pub fn as_pretty(&self) -> SmtPrettyPrinter {
        translate_smt_to_term(self)
    }
}

/// Represents a constructor for a datatype in SMT-LIB.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
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

impl<U: SmtParam> FromIterator<Smt<U>> for SmtFile<U> {
    /// Creates an `SmtFile` from an iterator of `Smt` commands.
    fn from_iter<T: IntoIterator<Item = Smt<U>>>(iter: T) -> Self {
        SmtFile {
            content: iter.into_iter().collect(),
        }
    }
}

impl<U: SmtParam> Smt<U> {
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
    pub fn mk_query(query: SmtFormula<U>) -> Self
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

impl<U: SmtParam> Smt<U>
where
    U::SVar: Eq,
{
    /// Creates an SMT assert command with an optimised formula.
    pub fn mk_assert(f: SmtFormula<U>) -> Self {
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
}

impl<U: SmtParam> Display for Smt<U> {
    /// Formats the SMT command for display in SMT-LIB format.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Smt::Assert(formula) => writeln!(f, "(assert {formula})"),
            #[cfg(feature = "vampire")]
            Smt::AssertTh(formula) => {
                writeln!(
                    f,
                    "; not smt-compliant. Change to `(assert ...)` to be compliant while \
                     retaining the semantics"
                )?;
                writeln!(f, "(assert-theory {formula})")
            }
            #[cfg(feature = "cryptovampire")]
            Smt::AssertGround { sort, formula } => {
                writeln!(
                    f,
                    "; cryptovampire specific. Needs a modified version of vampire"
                )?;
                writeln!(f, "(assert-ground {sort} {formula})")
            }
            #[cfg(feature = "vampire")]
            Smt::AssertNot(formula) => {
                writeln!(
                    f,
                    "; not smt-compliant. Change to `(assert (not ...))` to be compliant while \
                     retaining the semantics"
                )?;
                writeln!(f, "(assert-not {formula})")
            }
            Smt::DeclareFun { fun, args, out } =>
            // writeln!(
            //     f,
            //     "(declare-fun {fun} {} {out})",
            //     Arr::simple(args.as_slice())
            // )
            {
                write_par(f, |f| {
                    write!(f, "declare-fun {fun} ")?;
                    write_list(args, f, |f, arg| write!(f, "{arg} "))?;
                    write!(f, "{out}")
                })
            }
            Smt::DeclareSort(s) => writeln!(f, "(declare-sort {s} 0)"),
            Smt::DeclareSortAlias { from, to } => writeln!(f, "(define-sort {from} () {to})"),
            #[cfg(feature = "cryptovampire")]
            Smt::DeclareSubtermRelation(fun, funs) => {
                writeln!(
                    f,
                    "; cryptovampire specific. Needs a modified version of vampire"
                )?;
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
                writeln!(
                    f,
                    "; cryptovampire specific. Needs a modified version of vampire"
                )?;
                write_par(f, |f| {
                    write!(f, "declare-rewrite ")?;
                    write_par(f, |f| {
                        write!(f, "forall ")?;
                        write_list(vars, f, |f, var| write!(f, "({var} {})", var.sort_ref()))?;
                        write_par(f, |f| {
                            match rewrite_fun {
                                RewriteKind::Bool => write!(f, "= "),
                                RewriteKind::Other(fun) => write!(f, "{fun} "),
                            }?;
                            write!(f, " {lhs} {rhs}")
                        })
                    })
                })
                // write!(f, "(declare-rewrite ")?;
                // {
                //     write!(f, "(forall {} (", Arr::simple(vars.as_slice()))?;
                //     match rewrite_fun {
                //         RewriteKind::Bool => write!(f, "="),
                //         RewriteKind::Other(fun) => write!(f, "{fun}"),
                //     }?;
                //     write!(f, " {lhs} {rhs})")?;
                // }
                // writeln!(f, ")")
            }
            Smt::DeclareDatatypes { sorts, cons } => write_par(f, |f| {
                write!(f, "declare-datatypes")?;

                write_list(sorts, f, |f, s| write!(f, "({s} 0)"))?;

                write_list(cons, f, |f, cons| {
                    write_list(cons, f, |f, SmtCons { fun, sorts, dest }| {
                        write_par(f, |f| {
                            write!(f, "{fun} ")?;
                            for (i, (s, dest)) in izip!(sorts, dest).enumerate() {
                                match dest {
                                    Some(dest) => write!(f, "({dest} {s}) "),
                                    None => write!(f, "({fun}$_dest_{i:} {s}) "),
                                }?
                            }
                            Ok(())
                        })
                    })
                })
            }),
            Smt::Comment(c) => {
                for c in c.split('\n') {
                    writeln!(f, "; {c}")?
                }
                Ok(())
            }
            Smt::CheckSat => writeln!(f, "(check-sat)"),
            Smt::GetProof => writeln!(f, "(get-proof)"),
            Smt::SetOption(option, arg) => writeln!(f, "(set-option :{option} {arg})"),
            Smt::SetLogic(logic) => writeln!(f, "(set-logic {logic})"),
        }
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
