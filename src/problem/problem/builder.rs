use std::rc::Rc;

use crate::{
    container::Container,
    formula::{
        formula::RichFormula,
        function::{evaluate::Evaluator, term_algebra::name::NameCaster, Function},
        sort::Sort,
    }, problem::crypto_assumptions::CryptoAssumption,
};

use super::Problem;

#[derive(Debug)]
pub struct PblFromParser<'bump> {
    pub llc: LongLivedContent<'bump>,
    pub functions: Vec<Function<'bump>>,
    pub sorts: Vec<Sort<'bump>>,
    pub assertions: Vec<RichFormula<'bump>>,
    pub lemmas: Vec<RichFormula<'bump>>,
    pub query: Box<RichFormula<'bump>>,

    pub steps: Vec<TmpStep<'bump>>,
    pub cells: Vec<TmpCells<'bump>>,
    pub crypto_assertions: Vec<CryptoAssumption<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpStep<'bump> {
    pub name: String,
    pub args: Vec<Sort<'bump>>,
    pub assignements: Vec<TmpAssignements<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpCells<'bump> {
    pub name: String,
    pub args: Vec<Sort<'bump>>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct TmpAssignements<'bump> {
    pub step_idx: usize,
    pub cell_idx: usize,
    pub args: Vec<RichFormula<'bump>>,
    pub content: Box<RichFormula<'bump>>,
}

#[derive(Debug)]
pub struct LongLivedContent<'bump> {
    pub container: &'bump Container<'bump>,
    pub evaluator: Rc<Evaluator<'bump>>,
    pub name_caster: Rc<NameCaster<'bump>>,
}

impl<'bump> Into<Problem<'bump>> for PblFromParser<'bump> {
    fn into(self) -> Problem<'bump> {
        let PblFromParser {
            llc,
            functions,
            sorts,
            assertions,
            lemmas,
            query,
            steps,
            cells,
            crypto_assertions,
        } = self;
        let LongLivedContent {
            container,
            evaluator,
            name_caster,
        } = llc;

        todo!()
    }
}
