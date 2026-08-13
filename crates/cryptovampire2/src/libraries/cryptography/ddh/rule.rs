use std::borrow::Cow;

use egg::{Pattern, SearchMatches, Searcher};
use golgge::Rule;
use itertools::{Itertools, chain};

use super::vars::*;
use crate::libraries::DDH;
use crate::libraries::utils::Side::{Left, Right};
use crate::libraries::utils::{FreshNonceSet, RuleWithFreshNonce};
use crate::problem::{PAnalysis, RcRule};
use crate::terms::{EQUIV, Function, FunctionFlags, NONCE, Sort};
use crate::{CVProgram, Lang, rexp};

#[derive(Debug, Clone)]
pub struct DDHRule {
    #[allow(dead_code)]
    index: usize,
    goal_left: Pattern<Lang>,
    goal_right: Pattern<Lang>,
    deps: [Pattern<Lang>; 2],
}

impl DDHRule {
    pub fn new(
        DDH {
            index,
            g,
            exp,
            candidate_m,
            search_m,
            subst,
            ..
        }: &DDH,
    ) -> Self {
        Self {
            index: *index,
            goal_left: Pattern::from(&rexp!((EQUIV #U #V (candidate_m #M #NA #NB) #B))),
            goal_right: Pattern::from(&rexp!((EQUIV #U #V  #B (candidate_m #M #NA #NB)))),
            deps: [
                rexp!((search_m #NA #NB #NC #M true)),
                rexp!((subst #SIDE #U #V (exp g (NONCE #NC)) (search_m #NA #NB #NC #M true) #B)),
            ]
            .map(|x| Pattern::from(&x)),
        }
    }
}

impl<'pbl> Rule<Lang, PAnalysis<'pbl>, RcRule> for DDHRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("ddh")
    }

    fn search(&self, prgm: &mut CVProgram<'pbl>, goal: egg::Id) -> golgge::Dependancy {
        let matches = chain![
            self.goal_left
                .search_eclass(prgm.egraph(), goal)
                .map(|m| (Left, m)),
            self.goal_right
                .search_eclass(prgm.egraph(), goal)
                .map(|m| (Right, m)),
        ]
        .collect_vec();

        let mut ret = Vec::new();

        for (side, SearchMatches { substs, .. }) in matches {
            let side = side.get_id(prgm.egraph_mut());
            for mut subst in substs {
                subst.insert(SIDE.as_egg(), side);
                let [m, na, nb, b] = [M, NA, NB, B].map(|v| *subst.get(v.as_egg()).unwrap());
                for nc in self.generate_fresh_nonce(prgm, [m, na, nb], [b]) {
                    subst.insert(NC.as_egg(), nc);
                    ret.push(
                        self.deps
                            .clone()
                            .map(|g| g.apply_susbt(prgm.egraph_mut(), &subst)),
                    )
                }
            }
        }
        ret.into_iter().collect()
    }
}

impl RuleWithFreshNonce for DDHRule {
    fn get_set_mut<'a>(&self, pbl: &'a mut crate::Problem) -> &'a mut FreshNonceSet {
        &mut pbl.state.n_ddh
    }

    fn get_set<'a>(&self, pbl: &'a crate::Problem) -> &'a FreshNonceSet {
        &pbl.state.n_ddh
    }

    fn get_bound(&self, pbl: &crate::Problem) -> Option<usize> {
        Some(pbl.config.ddh_limit)
    }

    fn mk_fresh_function(&self, pbl: &mut crate::Problem) -> Function {
        pbl.declare_function()
            .flag(FunctionFlags::NONCE | FunctionFlags::FRESH)
            .output(Sort::Nonce)
            .fresh_name("ddh_c")
            .call()
    }
}
