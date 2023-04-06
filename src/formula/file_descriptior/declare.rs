use crate::formula::{function::Function, sort::Sort};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Delcare<'bump> {
    Sort(Sort<'bump>),
    FreeFunction(Function<'bump>),
    DataTypes(Vec<DataType<'bump>>),
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
