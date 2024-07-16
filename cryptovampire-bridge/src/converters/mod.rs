
use thiserror::Error;

mod stage0;
mod stage1;
mod stage2;

#[derive(Debug, Error, Ord, Eq, PartialEq, PartialOrd, Clone)]
enum ConversiontError {
    #[error("unsupported binder")]
    UnsupportedBinder,
    #[error("unsuported macro: frame and global macros are not supported")]
    UnsupportedMacro,
    #[error("The fun constructor is misplaced")]
    MisplacedFun,
    #[error("Unsupported head. (usually because an apllied Name or Macros was put as a head")]
    UnssupportedHead,
    #[error("A binder has parameters that aren't variables")]
    NonVariableInQuantifier,
    #[error("The only supported binders are forall, exists and fins such that.")]
    UnssupportedQuantifier,
    #[error(
        "The problem makes use of high order functions which cannot be simplified by CryptoVampire"
    )]
    HighOrder,
    #[error("Diffs don't inlude the same number of protocol each time")]
    InconsistenDiff,
    #[error("Wrong number of arguments, expected {expected:}, got {got:}")]
    WrongNumberOfArguements { expected: usize, got: usize },
    #[error("A variable is not assigned")]
    UnassignedVariable,
    #[error("Other converstion error: {0}")]
    Other(Box<str>),
}

#[allow(non_camel_case_types)]
type utuple = u8;

#[derive(Debug, Clone)]
enum SQuant {
    Forall,
    Exists,
    FindSuchThat,
}

type Result<A> = std::result::Result<A, ConversiontError>;
