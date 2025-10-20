use std::borrow::Cow;

use cryptovampire_macros::smt;
use cryptovampire_smt::{IntoSmt, SmtFormula, VarInner};
use logic_formula::{Destructed, Formula};

use crate::{terms::{RecFOFormula, Variable}, LangVar, MSmtFormula};