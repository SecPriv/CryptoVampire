use std::{hash::Hash, rc::Rc};

use qcell::LCell;

use crate::formula::function::Function;

#[derive(Clone)]
pub struct PreRef<'id, T> {
    vec: Rc<LCell<'id, Vec<T>>>,
    i: usize,
}

impl<'id, T> PartialEq for PreRef<'id, T> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.vec, &other.vec) && self.i == other.i
    }
}
impl<'id, T> Eq for PreRef<'id, T> {}

impl<'id, T> Hash for PreRef<'id, T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.vec).hash(state);
        self.i.hash(state);
    }
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PreFunction<'bump>{
    Static(Function<'bump>),
    BaseTA,
    TAQuantifier,
    
};
pub type PreFunctionRef<'id> = PreRef<'id, PreFunction>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PreSort();
pub type PreSortRef<'id> = PreRef<'id, PreSort>;

#[derive(PartialEq, Eq, Hash, Clone)]
pub struct PreVariable<'id> {
    id: usize,
    sort: PreSortRef<'id>,
}

#[derive(PartialEq, Eq, Hash, Clone)]
pub enum PreFormula<'id> {
    Var(PreVariable<'id>),
    Application {
        fun: PreFunctionRef<'id>,
        args: Vec<PreFormula<'id>>,
    },
}
