use std::collections::HashMap;

use pest::error::Error;
use pest_derive::Parser;

use crate::{formula::{function::Function, sort::Sort, formula::RichFormula}, container::Container};

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
struct MainParser;

type E = Error<Rule>;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum PFunRef<'str, 'bump> {
    MFun(Function<'bump>),
    PFun(&'str str),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct PFun<'str, 'bump> {
    name: &'str str,
    args: Vec<PSortRef<'str, 'bump>>,
    out: PSortRef<'str, 'bump>,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct PSort<'str> {
    name: &'str str,
}
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum PSortRef<'str, 'bump> {
    MSort(Sort<'bump>),
    PSort(&'str str),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct PVarRef<'str> {
    name: &'str str,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct PVar<'str, 'bump> {
    name: &'str str,
    sort: PSortRef<'str, 'bump>,
}

#[derive(Debug, Clone)]
struct ParisingEnv<'str, 'bump> {
    container: &'bump Container<'bump>,
    variables: HashMap<&'str str, RichFormula<'bump>>
}

impl<'str, 'bump> ParisingEnv<'str, 'bump> {
}