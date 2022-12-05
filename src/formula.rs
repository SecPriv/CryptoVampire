use std::rc::Rc;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone)]
pub enum Formula<F = RcFunction> {
    Var(String),
    Fun(F, Vec<Formula<F>>),
    Qnt(Quantifier, String, Box<Formula<F>>),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum Quantifier {
    Forall,
    Exists,
}

#[derive(Eq, Hash, Debug)]
pub struct RcFunction<S = String>(Rc<Function<S>>);

impl<S: PartialEq> PartialEq for RcFunction<S> {
    fn eq(&self, other: &Self) -> bool {
        Rc::as_ptr(&self.0) == Rc::as_ptr(&other.0)
    }
}
impl<S: PartialOrd> PartialOrd for RcFunction<S> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match self.0.partial_cmp(&other.0) {
            Some(std::cmp::Ordering::Equal) => {
                Rc::as_ptr(&self.0).partial_cmp(&Rc::as_ptr(&other.0))
            }
            o => o,
        }
    }
}
impl<S: Ord> Ord for RcFunction<S> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match self.0.cmp(&other.0) {
            std::cmp::Ordering::Equal => Rc::as_ptr(&self.0).cmp(&Rc::as_ptr(&other.0)),
            o => o,
        }
    }
}
impl<S> Clone for RcFunction<S> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Clone)]
pub struct Function<S> {
    name: String,
    input_sorts: Vec<S>,
    output_sort: S,
}

impl<S> Function<S> {
    pub fn arity(&self) -> usize {
        self.input_sorts.len()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct CNF<F = RcFunction>(Vec<Vec<Formula<F>>>);
