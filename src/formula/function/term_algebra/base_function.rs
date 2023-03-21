use bumpalo::boxed::Box;

use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerBaseFunction<'bump> {
    name: Box<'bump, str>,
    args: Box<'bump, [Sort<'bump>]>,
    out: Sort<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BaseFunction<'bump> {
    Eval(&'bump BaseFunction<'bump>),
    Base(BaseFunction<'bump>),
}
