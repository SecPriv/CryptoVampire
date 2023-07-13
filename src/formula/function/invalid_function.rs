use crate::{formula::sort::Sort, utils::string_ref::StrRef};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InvalidFunction<'bump> {
    pub name: Option<StrRef<'bump>>,
    pub args: Option<Vec<Sort<'bump>>>,
    pub sort: Option<Sort<'bump>>,
}

impl<'bump> InvalidFunction<'bump> {
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(AsRef::as_ref)
    }

    pub fn args(&self) -> Option<&[Sort<'bump>]> {
        self.args.as_ref().map(Vec::as_slice)
    }

    pub fn sort(&self) -> Option<Sort<'bump>> {
        self.sort
    }
}
