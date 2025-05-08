use egg::{EClass, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr};
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use utils::{ereturn, ereturn_if, iter_array::IntoArray};

use crate::{
    formula::{
        analysis::DependancyAnalysis,
        grammar::{Op, TA},
        protocol::Protocol,
    },
    mutils::SubtermIterator,
};

#[derive(Debug, Clone)]
pub struct PRF<'p> {
    ptcl: &'p Protocol<TA>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Candidate {
    /// [Id] of `hash(m, k)`
    id: Id,
    m: Id,
    k: Id,
}

#[derive(Debug, Clone, Copy)]
struct Instance<'a> {
    term: Id,
    candidates: &'a [Candidate],
    i: usize
}


impl<'p> PRF<'p> {
    fn run(&self, egraph: &EGraph<TA, DependancyAnalysis>) {
        egraph
            .classes_for_op(&Op::Equiv)
            .into_iter()
            .flatten()
            .filter_map(|id| {
                let hash_substerms= SubtermIterator::new(egraph, id).flat_map(|e| {
                    e.iter().filter_map(|l| match l.op() {
                        Op::Hash => {
                            let [m, k] = l.args_arr().unwrap(); // shouldn't be possible to crash here
                            let k = TA::get_name(egraph, k)?;
                            Some(Candidate { id: e.id, m, k })
                        }
                        _ => None,
                    })
                }).unique().collect_vec();
                (!hash_substerms.is_empty()).then(|| (id, hash_substerms))
            });
        todo!()
    }
}

impl<'a> Instance<'a> {
    // TODO: prove this
    fn run(&self, egraph: &EGraph<TA, DependancyAnalysis>, ptcl: &Protocol<TA>) -> Option<RecExpr<TA>>{
        let Self { term, candidates, i } = *self;
        let Candidate { m, k,.. } = candidates[i];
        let n:Id = todo!();
        egraph[term].data

        todo!()
    }
}