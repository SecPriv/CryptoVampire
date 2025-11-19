use egg::{Analysis, EGraph, Id, Pattern};
use golgge::Program;
use itertools::{Itertools, chain};
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::{ebreak_if, ebreak_let, implvec};

use crate::{
    CVProgram, Lang, Problem,
    problem::PAnalysis,
    rexp,
    terms::{Formula, Function, IS_FRESH_NONCE, NONCE, utils::iter_egraph::iter_descendants_lang},
};

#[dynamic]
static PATTERN_FALSE: Pattern<Lang> = Pattern::from(&rexp!(false));

pub trait RuleWithFreshNonce {
    fn get_set_mut<'a>(&self, pbl: &'a mut Problem) -> &'a mut FxHashSet<Id>;
    fn get_set<'a>(&self, pbl: &'a Problem) -> &'a FxHashSet<Id>;

    /// how much can be generated?
    fn get_bound(&self, pbl: &Problem) -> Option<usize>;

    fn can_have_children(f: &Function) -> bool {
        f.is_egg_binder() || (f.is_part_of_F() && !f.is_alias())
    }
    fn all_nonce_descendants<N: Analysis<Lang>>(
        egraph: &EGraph<Lang, N>,
        ancestors: implvec!(Id),
    ) -> FxHashSet<Id> {
        iter_descendants_lang(egraph, ancestors, Self::can_have_children)
            .filter(|&x| x.head == NONCE)
            .map(|x| x.args[0])
            .collect()
    }

    fn mk_fresh_function(&self, pbl: &mut Problem) -> Function;

    fn generate_fresh_nonce<'a, R>(
        &self,
        pgrm: &mut CVProgram<'a, R>,
        // we need to avoid here
        self_ids: implvec!(Id),
        // we'd like to pick in here
        other_ids: implvec!(Id),
    ) -> Vec<Id> {
        // try to look for
        'a: {
            let egraph = pgrm.egraph();
            let nonces = self.get_set(egraph.analysis.pbl());
            ebreak_if!('a, nonces.is_empty());

            let nonces: FxHashSet<_> = nonces
                .difference(&Self::all_nonce_descendants(egraph, self_ids))
                .copied()
                .collect();
            ebreak_if!('a, nonces.is_empty());

            let all_other = Self::all_nonce_descendants(egraph, other_ids);

            let with_other = nonces.intersection(&all_other).copied().collect_vec();
            ebreak_if!('a, with_other.is_empty());

            let mut without_other = nonces.difference(&all_other).copied();
            ebreak_let!('a, let Some(without_other)= without_other.next());

            return chain![with_other, [without_other]].collect();
        }

        // else generate new nonce
        if let Some(limit) = self.get_bound(pgrm.egraph().analysis.pbl())
            && self.get_set(pgrm.egraph().analysis.pbl()).len() <= limit
        {
            let nonces = pgrm
                .egraph()
                .analysis
                .pbl()
                .functions()
                .nonces()
                .cloned()
                .collect_vec();
            let fun = self.mk_fresh_function(pgrm.egraph_mut().analysis.pbl_mut());
            let n = pgrm.egraph_mut().add(fun.app_id([]));
            pgrm.egraph_mut().add(IS_FRESH_NONCE.app_id([n]));

            for n in nonces {
                let vars = n.signature.mk_vars().into_iter().map(Formula::Var);
                let from = Pattern::from(&rexp!((= (n #vars*) fun)));

                let rw_rule = egg::Rewrite::new(
                    format!("{fun} {n} distinctiveness"),
                    from,
                    PATTERN_FALSE.clone(),
                )
                .unwrap();
                println!("adding {rw_rule:?}");
                pgrm.add_eq_rule(rw_rule);
            }

            self.get_set_mut(pgrm.egraph_mut().analysis.pbl_mut())
                .insert(n);
        }

        self.get_set(pgrm.egraph().analysis.pbl())
            .iter()
            .cloned()
            .collect()
    }
}
