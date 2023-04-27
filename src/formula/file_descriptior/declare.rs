use crate::{
    container::{NameFinder, ScopeAllocator},
    formula::{
        function::{Function, InnerFunction},
        sort::Sort,
    },
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Declaration<'bump> {
    Sort(Sort<'bump>),
    SortAlias { from: Sort<'bump>, to: Sort<'bump> },
    FreeFunction(Function<'bump>),
    DataTypes(Vec<DataType<'bump>>),
    Subterm(Subterm<'bump>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DataType<'bump> {
    pub sort: Sort<'bump>,
    pub constructor_destructors: Vec<ConstructorDestructor<'bump>>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ConstructorDestructor<'bump> {
    pub constructor: Function<'bump>,
    pub destructor: Vec<Function<'bump>>,
}

impl<'bump> ConstructorDestructor<'bump> {
    pub fn new_unused(
        container: &'bump (impl ScopeAllocator<'bump, InnerFunction<'bump>>
                    + NameFinder<Function<'bump>>),
        f: Function<'bump>,
    ) -> Self {
        Self {
            constructor: f,
            destructor: Function::new_unused_destructors(container, f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Subterm<'bump> {
    pub name: String,
    pub functions: Vec<Function<'bump>>,
}