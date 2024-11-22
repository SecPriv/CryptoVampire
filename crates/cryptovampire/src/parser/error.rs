use std::fmt::Display;

use thiserror::Error;

#[derive(Debug, Clone, Error)]
pub enum ParsingError {
    Undefined {
        iden: Box<str>,
        kind: Box<str>,
        hint: Option<Box<str>>,
    },
    AlreadyInUse {
        iden: Box<str>,
        kind: Box<str>,
    },
    OneOff(&'static str),
}

impl Display for ParsingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParsingError::Undefined { iden, kind, hint } => {
                write!(f, "undefined {kind:} : \"{iden:}\"")?;
                if let Some(hint) = hint {
                    write!(f, "\nhint: {hint:}")?;
                }
                Ok(())
            }
            ParsingError::AlreadyInUse { iden, kind } => {
                write!(f, "the {kind:} name \"{iden:}\" is already in use")
            }
            ParsingError::OneOff(s) => s.fmt(f),
        }
    }
}

impl ParsingError {
    pub fn undefined_sort(s: &str) -> Self {
        Self::Undefined {
            iden: s.into(),
            kind: "sort".into(),
            hint: None,
        }
    }
    pub fn undefined_function(s: &str) -> Self {
        Self::Undefined {
            iden: s.into(),
            kind: "function".into(),
            hint: Some("If you looked for a macro, maybe you forgot the '!'".into()),
        }
    }

    pub fn already_defined(kind: &str, iden: &str) -> Self {
        Self::AlreadyInUse {
            iden: iden.into(),
            kind: kind.into(),
        }
    }
}
