pub mod ast;
mod parser;

use ast::INIT_STEP_AST;
pub use parser::{parse_pbl_from_ast};
use static_init::dynamic;

use std::borrow::Borrow;

use pest_derive::Parser;
use utils::{string_ref::StrRef, traits::NicerError};

/// Errors used thoughout parsing
mod error;
pub use error::{InputError, Location, WithLocation};

/// The [Pstr] trait wich serves as a trick to gather many traits
mod pstr;
pub use pstr::*;

pub const USED_KEYWORDS: &'static [&'static str] = &[
    "and",
    "or",
    "not",
    "ite",
    "assert",
    "assert-not",
    "assert-theory",
    "rewrite",
    "subterm",
    "True",
    "False",
    "true",
    "false",
    "implies",
    "forall",
    "exists",
    "match",
    "declare-datatype",
    "declare-fun",
    "declare-sort",
    "define-fun",
    "define-fun-rec",
    "define-sort",
    "Int",
    "Real",
    "Array",
];

pub type MResult<T> = std::result::Result<T, error::InputError>;

// -----------------------------------------------------------------------------
// --------------------------------- parser ------------------------------------
// -----------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;
