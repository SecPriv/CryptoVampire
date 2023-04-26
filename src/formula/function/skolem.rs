use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Skolem<'bump> {
    name: Box<str>,
    in_sort: Box<[Sort<'bump>]>,
    out_sort: Sort<'bump>
}

impl<'bump> Skolem<'bump> {
    pub fn out_sort(&self) -> &Sort<'bump> {
        &self.out_sort
    }

    pub fn in_sort(&self) -> &[Sort<'bump>] {
        self.in_sort.as_ref()
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}