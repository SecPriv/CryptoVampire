//! converted from https://github.com/symflower/smtfmt
//!
//! by Gemini (https://gemini.google.com/app/04a15fdad378fa4b)

use std::fmt::Display;

use utils::implvec;

/// Parsing logic
#[cfg(feature = "smt-parsing")]
mod parser;

pub(crate) use printing::format_term;
/// Formatter logic
mod printing;

pub use translation::translate_smt_to_term;
/// translation logic
mod translation;

#[cfg(feature = "smt-parsing")]
pub use leftovers::format_smtlib;
#[cfg(feature = "smt-parsing")]
mod leftovers;

#[cfg(feature = "smt-parsing")]
#[cfg(test)]
mod tests;

/// Represents the possible S-expression terms.
#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    SExpr(Vec<Term>, Option<String>), // S-expression, attached comment
    Atom(String, Option<String>),     // Atom, attached comment
    Comment(String),
    BlankLine(usize),
}

impl Term {
    fn sexpr(args: implvec!(Term)) -> Self {
        Self::SExpr(args.into_iter().collect(), None)
    }

    fn atom(arg: impl Display) -> Self {
        Self::Atom(arg.to_string(), None)
    }

    fn on_a_single_line(&self) -> bool {
        matches!(self, Term::Atom(_, _) | Term::Comment(_))
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{}", format_term(self, 0))
    }
}
