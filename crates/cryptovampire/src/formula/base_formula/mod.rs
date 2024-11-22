mod iterator;
mod tmp_formula;
use std::fmt::Display;

pub use tmp_formula::TmpFormula;
use utils::implvec;

use crate::error::{LocateHelper, LocationProvider};

/// A very simplified AST
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BaseFormula<B, F, V> {
    Binder {
        head: B,
        vars: Vec<V>,
        args: Vec<Self>,
    },
    App {
        head: F,
        args: Vec<Self>,
    },
    Var(V),
}

impl<B, F, V> BaseFormula<B, F, V> {
    pub fn new(head: F, args: implvec!(Self)) -> Self {
        Self::App {
            head,
            args: args.into_iter().collect(),
        }
    }

    pub fn new_const(head: F) -> Self {
        Self::App { head, args: vec![] }
    }
}

impl<B, F, V> Display for BaseFormula<B, F, V>
where
    B: Display,
    F: Display,
    V: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::App { head, args } => {
                write!(f, "{:}(", &head)?;
                for arg in args {
                    write!(f, "{:}, ", arg)?;
                }
                write!(f, ")")
            }
            Self::Binder { head, vars, args } => {
                write!(f, "{:}(", &head)?;
                for var in vars {
                    write!(f, "{:}, ", var)?;
                }
                write!(f, ") {{")?;
                for arg in args {
                    write!(f, "{:}; ", arg)?;
                }
                write!(f, "}}")
            }
            Self::Var(s) => s.fmt(f),
        }
    }
}

impl<'a, B, F, V> LocationProvider for &'a BaseFormula<B, F, V>
where
    B: Display,
    F: Display,
    V: Display,
{
    fn provide(self) -> crate::error::Location {
        ().help_provide(self)
    }
}
