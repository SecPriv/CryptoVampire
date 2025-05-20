use std::{borrow::Cow, collections::HashMap};

use logic_formula::egg::{SimplLang, SimplLangVar};
use protocol::Protocol;
use terms::Function;

pub mod protocol;
pub mod rules;
pub mod terms;

pub type Lang = SimplLang<Function>;
pub type LangVar = SimplLangVar<Function>;

#[derive(Debug, Default)]
pub struct Configuration {}

mod problem;
pub use problem::Problem;

pub(crate) mod utils;