use crate::Program;
use egg::{Analysis, Id, Language, RecExpr};

/// Basic prolog-like rules
mod prolog;
pub use prolog::{PrologRule, parser::PlOrRw};

// /// Calls vampire on a goal
// mod vampire;
// pub use vampire::VampireRule;

#[derive(Debug, PartialEq, Eq, Ord, PartialOrd, Hash, Clone, Default)]
pub struct Dependancy {
    inner: Vec<Vec<Id>>,
    cut: bool,
}

impl Dependancy {
    pub fn new(inner: Vec<Vec<Id>>) -> Self {
        Self { inner, cut: false }
    }

    pub fn inner(&self) -> &Vec<Vec<Id>> {
        &self.inner
    }

    pub fn cut(&self) -> bool {
        self.cut
    }

    pub fn set_cut(self, cut: bool) -> Self {
        Self { cut, ..self }
    }

    pub fn do_cut(self) -> Self {
        self.set_cut(true)
    }

    pub fn do_not_cut(self) -> Self {
        self.set_cut(false)
    }
}

pub trait Rule<L: Language, N: Analysis<L>> {
    fn search(&self, prgm: &mut Program<L, N>, goal: Id) -> Dependancy;

    fn rebuild(&self, _prgm: &Program<L, N>) {}
}

pub trait Fresh: Sized {
    fn mk_fresh() -> RecExpr<Self>;
}
