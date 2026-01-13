use std::borrow::Cow;

use egg::{Id, Pattern, SearchMatches, Searcher};
use golgge::{Dependancy, Program, Rule};
use itertools::{Itertools, chain};

use super::vars::*;
use crate::libraries::AEnc;
use crate::libraries::utils::Side::{Left, Right};
use crate::libraries::utils::{FreshNonceSet, RuleWithFreshNonce, TwoSortFunction};
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::{EQUIV, FRESH_NONCE, Function, FunctionFlags, NONCE, Sort};
use crate::{Lang, Problem, rexp};

pub fn mk_rules(_: &Problem, aenc: &AEnc) -> impl Iterator<Item = RcRule> {
    [EncKpRule::new(aenc).into_mrc()].into_iter()
}

struct EncKpRule {
    #[allow(dead_code)]
    aenc: usize,

    goal_left: Pattern<Lang>,
    goal_right: Pattern<Lang>,

    checks: [Pattern<Lang>; 4],
    new_goal: Pattern<Lang>,
}

impl EncKpRule {
    pub fn new(
        AEnc {
            enc,
            pk,
            index,
            subst,
            candidate: TwoSortFunction { m: candidate, .. },
            search_o: TwoSortFunction { m: search_o, .. },
            search_k: TwoSortFunction { m: search_k, .. },
            ..
        }: &AEnc,
    ) -> Self {
        let new_goal = if let Some(pk) = pk {
            Pattern::from(&rexp!((subst #SIDE #U #V
              (enc #M (NONCE #R) (pk (NONCE #K2))) (search_k #K #K2 #R #M #T true)
            #B)))
        } else {
            Pattern::from(&rexp!((subst #SIDE #U #V
              (enc #M (NONCE #R) (NONCE #K2)) (search_k #K #K2 #R #M #T true)
            #B)))
        };

        EncKpRule {
            aenc: *index,
            goal_left: Pattern::from(&rexp!((EQUIV #U #V (candidate #T #M #R #K) #B))),
            goal_right: Pattern::from(&rexp!((EQUIV #U #V #B (candidate #T #M #R #K)))),
            checks: [
                rexp!((search_o #K #M true)),
                rexp!((search_o #K2 #M true)),
                rexp!((search_k #K #K2 #R #M #T true)),
                rexp!((FRESH_NONCE #R #M true)),
            ]
            .map(|x| Pattern::from(&x)),
            new_goal,
        }
    }
}

impl<'a, R> Rule<Lang, PAnalysis<'a>, R> for EncKpRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("enc-kp")
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(
            f,
            "enc-kp(left:={}, right:={})",
            self.goal_left, self.goal_right
        )
    }

    fn search(&self, prgm: &mut Program<Lang, PAnalysis<'a>, R>, goal: Id) -> Dependancy {
        let matches = chain![
            self.goal_left
                .search_eclass(prgm.egraph(), goal)
                .map(|m| { (Left, m) }),
            self.goal_right
                .search_eclass(prgm.egraph(), goal)
                .map(|m| (Right, m)),
        ]
        .collect_vec();

        if matches.is_empty() {
            return Dependancy::impossible();
        }

        let mut ret = Vec::new();

        for (side, SearchMatches { substs, .. }) in matches {
            let side = side.get_id(prgm.egraph_mut());
            for mut subst in substs {
                subst.insert(SIDE.as_egg(), side);
                let [t, m, r, k, b] = [T, M, R, K, B].map(|v| *subst.get(v.as_egg()).unwrap());
                for k2 in self.generate_fresh_nonce(prgm, [t, m, r, k], [b]) {
                    subst.insert(K2.as_egg(), k2);
                    ret.push(
                        chain![&self.checks, [&self.new_goal]]
                            .map(|g| g.apply_susbt(prgm.egraph_mut(), &subst))
                            .collect_vec(),
                    )
                }
            }
        }
        ret.into_iter().collect()
    }
}

impl RuleWithFreshNonce for EncKpRule {
    fn get_set_mut<'a>(&self, pbl: &'a mut Problem) -> &'a mut FreshNonceSet {
        &mut pbl.state.n_enc_kp
    }

    fn get_set<'a>(&self, pbl: &'a Problem) -> &'a FreshNonceSet {
        &pbl.state.n_enc_kp
    }

    fn get_bound(&self, pbl: &Problem) -> Option<usize> {
        Some(pbl.config.enc_kp_limit)
    }

    fn mk_fresh_function(&self, pbl: &mut Problem) -> Function {
        pbl.declare_function()
            .fresh_name("k_enc_kp")
            .flags(FunctionFlags::NONCE | FunctionFlags::FRESH)
            .output(Sort::Nonce)
            .call()
    }
}
