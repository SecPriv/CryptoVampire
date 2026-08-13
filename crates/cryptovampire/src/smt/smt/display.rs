use std::fmt;

use super::{Smt, SmtFile, SmtFormula};
use crate::environement::traits::KnowsRealm;
use crate::smt::smt::SmtDisplay;

/// A wrapper that implements [`fmt::Display`] by writing the SMT representation
/// of the wrapped value.
///
/// The `env` is threaded through [`SmtDisplay::as_display`] so that callers can
/// pick the realm in which terms are rendered, but the realm doesn't currently
/// influence the printed string: the actual rendering is done by the [`Display`]
/// impl of the wrapped value.
#[derive(Debug, Copy, Clone)]
pub struct SmtDisplayer<T> {
    pub content: T,
}

impl<'bump> SmtDisplay<'bump> for SmtFormula<'bump> {
    fn as_display(&self, _env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer { content: self }
    }
}

impl<'bump> SmtDisplay<'bump> for Smt<'bump> {
    fn as_display(&self, _env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer { content: self }
    }
}

impl<'bump> SmtDisplay<'bump> for SmtFile<'bump> {
    fn as_display(&self, _env: &impl KnowsRealm) -> impl fmt::Display + '_ {
        SmtDisplayer { content: self }
    }
}

impl fmt::Display for SmtDisplayer<SmtFormula<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl fmt::Display for SmtDisplayer<&SmtFormula<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl fmt::Display for SmtDisplayer<Smt<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl fmt::Display for SmtDisplayer<&Smt<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.content)
    }
}

impl fmt::Display for SmtDisplayer<SmtFile<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for smt in &self.content.content {
            writeln!(f, "{}", smt)?;
        }
        Ok(())
    }
}

impl fmt::Display for SmtDisplayer<&SmtFile<'_>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for smt in &self.content.content {
            writeln!(f, "{}", smt)?;
        }
        Ok(())
    }
}
