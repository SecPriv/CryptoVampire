use crate::formula::sort::{InnerSort, Sort};

pub trait HasArity {
    fn arity(&self) -> usize;
}
pub trait HasInputSorts {
    type Iter: Iterator<Item = Sort<'a>>;
    fn input_sorts<'sort>(&'sort self) -> &'sort [Self::Ref];
}

pub trait HasOutputSort {
    type Ref: AsRef<InnerSort>;
    fn output_sort<'sort>(&'sort self) -> &'sort Self::Ref;
}

pub trait Named {
    fn name(&self) -> &str;
}

impl<T: HasInputSorts> HasArity for T {
    fn arity(&self) -> usize {
        self.input_sorts().len()
    }
}
