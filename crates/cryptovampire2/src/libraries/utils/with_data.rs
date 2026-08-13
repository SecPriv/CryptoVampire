use egg::{Analysis, EGraph, Id, Pattern};
use itertools::{Itertools, chain, izip};
use log::{trace, warn};
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::transposer::Transposable;
use utils::{ebreak_if, ebreak_let, implvec};

use crate::problem::{CurrentStep, PAnalysis, ProblemState};
use crate::terms::utils::iter_egraph::iter_descendants_lang;
use crate::terms::{Formula, Function, IS_FRESH_NONCE, NONCE, Sort, Substitution, Variable};
use crate::{CVProgram, Lang, Problem, rexp};

#[dynamic]
static PATTERN_FALSE: Pattern<Lang> = Pattern::from(&rexp!(false));

#[derive(Debug, Clone, Default)]
pub struct FreshNonceSet {
    /// contains all availbe nonces
    set: FxHashSet<Id>,
    /// contains only the 'fresh' ones (i.e., not the ones coming from the user)
    fresh: FxHashSet<Id>,
    /// User defined 'fresh' nonces
    extra_recipies: Vec<UserFreshNonce>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UserFreshNonce {
    variables: Vec<Variable>,
    nonce: Formula,
}

impl FreshNonceSet {
    pub fn is_empty(&self) -> bool {
        self.set.is_empty() || self.fresh.is_empty()
    }

    pub fn len(&self) -> usize {
        self.set.len() + self.fresh.len()
    }

    pub fn reset(&mut self) {
        self.set.clear();
        self.fresh.clear();
    }

    fn all(&self) -> &FxHashSet<Id> {
        &self.set
    }

    fn fresh(&self) -> &FxHashSet<Id> {
        &self.fresh
    }

    pub fn register_nonce(&mut self, variables: Vec<Variable>, nonce: Formula) {
        assert!(self.is_empty());

        self.extra_recipies
            .push(UserFreshNonce { variables, nonce });
    }

    pub fn register_idx<'pbl>(
        egraph: &mut EGraph<Lang, PAnalysis<'pbl>>,
        mself: impl for<'a> Fn(&'a mut EGraph<Lang, PAnalysis<'pbl>>) -> &'a mut Self,
        nidx: Option<Id>,
    ) {
        let recipies = mself(egraph).extra_recipies.clone();
        let mut subst = Substitution::default();
        for UserFreshNonce { variables, nonce } in recipies {
            if variables.is_empty() {
                let fresh_idx = nonce.add_to_egraph(egraph);
                mself(egraph).set.insert(fresh_idx);
                continue;
            }

            let idx = variables
                .iter()
                .map(|v| {
                    let mut arg_idx = ProblemState::ids_of_sort(egraph, v.get_sort()).collect_vec();
                    if let Some(nidx) = nidx
                        && v.get_sort()
                            == Some(
                                egraph[nidx]
                                    .nodes
                                    .iter()
                                    .map(|l| l.head.signature.output)
                                    .find(|s| s != &Sort::Any)
                                    .unwrap(),
                            )
                    {
                        arg_idx.push(nidx);
                    }

                    let CurrentStep { idx, args } = egraph
                        .analysis
                        .pbl()
                        .current_step()
                        .expect("a running problem with a current step");

                    let mut arg = Vec::with_capacity(arg_idx.len() + args.len());

                    arg.extend(
                        arg_idx
                            .into_iter()
                            .map(|id| Formula::try_from_id(egraph, id).unwrap()),
                    );

                    trace!(
                        "register_idx current step: {}",
                        egraph.analysis.pbl().get_step_fun(*idx).unwrap()
                    );

                    arg.extend(
                        args.iter()
                            .inspect(|f| debug_assert_eq!(f.arity(), 0))
                            .filter(|f| f.signature.output == v.get_sort().unwrap())
                            .map(|f| rexp!(f)),
                    );

                    arg
                })
                .collect_vec();

            for args in idx.as_slice().transpose() {
                subst.0.clear();
                subst
                    .0
                    .extend(izip!(&variables, args).map(|(v, f)| (v.clone(), f.clone())));
                let fresh_idx = nonce.apply(&subst).add_to_egraph(egraph);
                mself(egraph).set.insert(fresh_idx);
            }
        }
    }

    fn add(&mut self, id: Id) {
        self.fresh.insert(id);
        self.set.insert(id);
    }
}

pub trait RuleWithFreshNonce {
    fn get_set_mut<'a>(&self, pbl: &'a mut Problem) -> &'a mut FreshNonceSet;
    fn get_set<'a>(&self, pbl: &'a Problem) -> &'a FreshNonceSet;
    fn mk_fresh_function(&self, pbl: &mut Problem) -> Function;

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

    fn generate_fresh_nonce<'a, R>(
        &self,
        pgrm: &mut CVProgram<'a, R>,
        // we need to avoid here
        self_ids: implvec!(Id),
        // we'd like to pick in here
        other_ids: implvec!(Id),
    ) -> Vec<Id> {
        // try to look for commun nonce
        'a: {
            let egraph = pgrm.egraph();
            let nonces = self.get_set(egraph.analysis.pbl());
            trace!("nonces has {:} elements", nonces.len());
            ebreak_if!('a, nonces.is_empty());

            let to_avoid = Self::all_nonce_descendants(egraph, self_ids);

            let nonce_pool: FxHashSet<_> = nonces.all().difference(&to_avoid).copied().collect();

            let fresh_nonce_pool: FxHashSet<_> =
                nonces.fresh().difference(&to_avoid).copied().collect();

            trace!("nonce_pool has {:} elements", nonce_pool.len());
            trace!("fresh_nonce_pool has {:} elements", fresh_nonce_pool.len());
            ebreak_if!('a, nonce_pool.is_empty() || fresh_nonce_pool.is_empty());

            let all_other = Self::all_nonce_descendants(egraph, other_ids);

            let with_other = nonce_pool.intersection(&all_other).copied().collect_vec();
            trace!("with_other has {:} elements", with_other.len());
            ebreak_if!('a, with_other.is_empty());

            let mut without_other = fresh_nonce_pool.difference(&all_other).copied();
            ebreak_let!('a, let Some(without_other)= without_other.next());
            trace!("without_other is non-empty");

            return chain![with_other, [without_other]].collect();
        }

        // else generate new nonce
        if let Some(limit) = self.get_bound(pgrm.egraph().analysis.pbl())
            && self.get_set(pgrm.egraph().analysis.pbl()).fresh().len() >= limit
        {
            warn!("beyonf the limit")
        } else {
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
                trace!("adding {rw_rule:?}");
                pgrm.add_eq_rule(rw_rule);
            }

            self.get_set_mut(pgrm.egraph_mut().analysis.pbl_mut())
                .add(n);
        }

        self.get_set(pgrm.egraph().analysis.pbl())
            .all()
            .iter()
            .cloned()
            .collect()
    }
}
