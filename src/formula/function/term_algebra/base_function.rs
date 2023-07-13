use crate::formula::{function::Function, sort::Sort};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerBaseFunction<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    pub out: Sort<'bump>,
    pub eval_fun: Function<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BaseFunction<'bump> {
    Eval(&'bump BaseFunction<'bump>),
    Base(InnerBaseFunction<'bump>),
}

impl<'bump> InnerBaseFunction<'bump> {
    pub fn eval_fun(&self) -> Function<'bump> {
        self.eval_fun
    }

    pub fn out(&self) -> Sort<'bump> {
        self.out
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct BaseFunctionTuple<'bump> {
    pub main: Function<'bump>,
    pub eval: Function<'bump>,
}
