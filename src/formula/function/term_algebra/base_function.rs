
use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerBaseFunction<'bump> {
    name: Box< str>,
    args: Box< [Sort<'bump>]>,
    out: Sort<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BaseFunction<'bump> {
    Eval(&'bump BaseFunction<'bump>),
    Base(InnerBaseFunction<'bump>),
}
