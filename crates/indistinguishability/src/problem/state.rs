use egg::{EGraph, Id};
use log::trace;
use rustc_hash::FxHashSet;

use crate::Lang;
use crate::libraries::utils::FreshNonceSet;
use crate::problem::PAnalysis;
use crate::terms::{IS_INDEX, Sort};

#[derive(Debug, Clone, Default)]
pub struct ProblemState {
    /// already used nonces
    pub n_prf: FreshNonceSet,
    pub n_enc_kp: FreshNonceSet,
    pub n_ddh: FreshNonceSet,

    pub generated_ids: FxHashSet<Id>,
}

impl ProblemState {
    pub fn reset(&mut self) {
        let Self {
            n_prf,
            n_enc_kp,
            n_ddh,
            generated_ids,
        } = self;

        generated_ids.clear();
        n_prf.reset();
        n_enc_kp.reset();
        n_ddh.reset();
    }

    pub fn ids_of_sort<'pbl>(
        egraph: &EGraph<Lang, PAnalysis<'pbl>>,
        sort: Option<Sort>,
    ) -> impl Iterator<Item = Id> {
        egraph
            .analysis
            .pbl()
            .state
            .generated_ids
            .iter()
            .filter(move |x| {
                sort.is_none()
                    || egraph[**x]
                        .nodes
                        .iter()
                        .any(|l| Some(l.head.signature.output) == sort)
            })
            .copied()
    }

    pub fn get_self<'a, 'pbl>(egraph: &'a EGraph<Lang, PAnalysis<'pbl>>) -> &'a Self {
        &egraph.analysis.pbl().state
    }

    pub fn get_self_mut<'a, 'pbl>(egraph: &'a mut EGraph<Lang, PAnalysis<'pbl>>) -> &'a mut Self {
        &mut egraph.analysis.pbl_mut().state
    }

    fn sets(&self) -> [&FreshNonceSet; 3] {
        let Self {
            n_prf,
            n_enc_kp,
            n_ddh,
            generated_ids: _,
        } = self;
        [n_ddh, n_enc_kp, n_prf]
    }

    fn sets_mut(&mut self) -> [&mut FreshNonceSet; 3] {
        let Self {
            n_prf,
            n_enc_kp,
            n_ddh,
            generated_ids: _,
        } = self;
        [n_ddh, n_enc_kp, n_prf]
    }

    pub fn generate_fresh_idx<'pbl>(
        egraph: &mut EGraph<Lang, PAnalysis<'pbl>>,
        sort: Sort,
        name: &str,
    ) -> Id {
        assert!(matches!(sort, Sort::Index | Sort::Time));

        let new_f = egraph
            .analysis
            .pbl_mut()
            .declare_function()
            .output(sort)
            .fresh_name(name)
            .call();
        trace!("generate fresh idx: {new_f}:{sort}");

        let new_var = egraph.add(Lang::new(new_f, []));
        if sort == Sort::Index {
            egraph.add(IS_INDEX.app_id([new_var]));
        }

        Self::get_self_mut(egraph).generated_ids.insert(new_var);

        Self::propagate(egraph, Some(new_var));

        new_var
    }

    fn propagate<'pbl>(egraph: &mut EGraph<Lang, PAnalysis<'pbl>>, new_var: Option<Id>) {
        let mut i = 0;
        while i < Self::get_self(egraph).sets().len() {
            FreshNonceSet::register_idx(egraph, |e| Self::get_self_mut(e).sets_mut()[i], new_var);
            i += 1;
        }
    }

    pub fn init_egraph<'pbl>(egraph: &mut EGraph<Lang, PAnalysis<'pbl>>) {
        assert!(Self::get_self(egraph).sets().iter().all(|s| s.is_empty()));
        Self::propagate(egraph, None);
    }
}
