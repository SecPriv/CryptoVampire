pub mod ast;
#[allow(clippy::module_inception)]
mod parser;

use std::borrow::Borrow;

use ast::INIT_STEP_AST;
pub use parser::parse_pbl_from_ast;
use pest_derive::Parser;
use static_init::dynamic;
use utils::string_ref::StrRef;
use utils::traits::NicerError;

/// Errors used thoughout parsing
// mod error;
// pub use error::{InputError, Location, WithLocation};

/// The [Pstr] trait wich serves as a trick to gather many traits
mod pstr;
pub use pstr::*;
pub mod error;

mod location;

pub const USED_KEYWORDS: &[&str] = &[
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

// pub type MResult<T> = std::result::Result<T, error::InputError>;

// -----------------------------------------------------------------------------
// --------------------------------- parser ------------------------------------
// -----------------------------------------------------------------------------

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;
