use thiserror::Error;
use utils::iter_array;

pub(crate) mod json;
// mod converters;

#[derive(Debug, Error, Ord, Eq, PartialEq, PartialOrd, Clone)]
pub enum ConversiontError {
    #[error("unsupported binder")]
    UnsupportedBinder,
    #[error("unsuported macro: frame and global macros are not supported")]
    UnsupportedMacro,
    #[error("The fun constructor is misplaced")]
    MisplacedFun,
    #[error("Unsupported head. (usually because an applied Name or Macros was put as a head")]
    UnssupportedHead,
    #[error("A binder has parameters that aren't variables")]
    NonVariableInQuantifier,
    #[error("The only supported binders are forall, exists and fins such that.")]
    UnsupportedQuantifier,
    #[error("More high order than CryptoVampire can handle")]
    TooMuchHighOrder,
    #[error("Diffs don't inlude the same number of protocol each time")]
    InconsistenDiff,
    #[error("Wrong number of arguments, expected {expected:}, got {got:}")]
    WrongNumberOfArguements { expected: usize, got: usize },
    #[error("A variable is not assigned")]
    UnassignedVariable,
    #[error("Invalid Diff operators. (Incosistent or 0 arity)")]
    InvalidDiff,
    #[error("More polymorphism than CryptoVampire can handle")]
    TooMuchPolymorphism,
    #[error("Undeclared name, operator, ...")]
    UndeclaredOp,
    #[error("Other converstion error: {0}")]
    Other(Box<str>),
}
