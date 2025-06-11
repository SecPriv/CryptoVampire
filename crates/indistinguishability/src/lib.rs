use std::{borrow::Cow, collections::HashMap};

use logic_formula::egg::{SimplLang, SimplLangVar};
use protocol::Protocol;
use terms::Function;

pub mod protocol;
pub mod rules;
pub mod terms;

pub static SIZE: usize = 3;
pub type Lang = SimplLang<Function, SIZE>;
pub type LangVar = SimplLangVar<Function, SIZE>;

#[derive(Debug, Default)]
pub struct Configuration {}

mod problem;
pub use problem::Problem;

pub(crate) mod utils;

use std::io::Write;

pub fn init_logger() {
    env_logger::Builder::new()
        .format(|buf, record| {
            if record.file().map(|s| s.contains("egg")) != Some(true) {
                let str = record.args().to_string().replace("\n", "\n\t");
                writeln!(
                    buf,
                    "[{}] in {}:{}\n\t{}",
                    record.level(),
                    record.file().unwrap_or("unknown"),
                    record.line().unwrap_or(0),
                    str
                )
            } else {
                Ok(())
            }
        })
        .parse_default_env()
        .init();
}
