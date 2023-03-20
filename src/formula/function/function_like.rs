use crate::formula::sort::Sort;

pub trait HasArity {
    fn arity(&self) -> usize;
}
pub trait HasInputSorts<'sort> {
    fn input_sorts(&self) -> &[Sort<'sort>];
}

pub trait HasOutputSort<'sort> {
    fn output_sort(&self) -> Sort<'sort>;
}

pub trait Named {
    fn name(&self) -> &str;
}

impl<'sort, T: HasInputSorts<'sort>> HasArity for T {
    fn arity(&self) -> usize {
        self.input_sorts().len()
    }
}
