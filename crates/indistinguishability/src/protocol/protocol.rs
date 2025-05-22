use egg::RecExpr;

use crate::Lang;

use super::Step;
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Protocol {
    pub name: RecExpr<Lang>,
    pub steps: Vec<Step>,
}

