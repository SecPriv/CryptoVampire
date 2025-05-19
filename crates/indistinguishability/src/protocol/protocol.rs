use egg::RecExpr;

use super::Step;
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Protocol<L> {
    pub name: RecExpr<L>,
    pub steps: Vec<Step<L>>,
}

impl<L> Protocol<L> {}
