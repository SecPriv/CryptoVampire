use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Predicate<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    pub out: Sort<'bump>
}