use crate::formula::sort::Sort;

/// A function that needs to exists for one reason or another but should never be used
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Unused<'bump> {
    pub name: String,
    pub in_sorts: Box<[Sort<'bump>]>,
    pub out_sort: Sort<'bump>
}