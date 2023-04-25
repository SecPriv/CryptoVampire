use crate::formula::{
    function::{subterm, Function},
    sort::Sort,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Declaration<'bump> {
    Sort(Sort<'bump>),
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Subterm<'bump> {
    pub name: String,
    pub functions: Vec<Function<'bump>>,
}
