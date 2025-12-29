use anyhow::Context;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use log::trace;
use utils::ereturn_let;

use super::vars::*;
use crate::libraries::DDH;
use crate::libraries::ddh::ProofHints;
use crate::libraries::substitution::{PSArgs, ProofLike, ProofSubstitution};
use crate::problem::{CVRuleTrait, PAnalysis, PRule, RcRule};
use crate::terms::{EQUIV_WITH_SIDE, Function};
use crate::{CVProgram, Lang, Problem, rexp};

pub fn mk_rules(_: &Problem, aenc: &DDH) -> impl Iterator<Item = RcRule> {
    [SubstRule::new(aenc).into_mrc()].into_iter()
}

#[derive(Debug, Clone)]
struct SubstRule {
    #[allow(dead_code)]
    aenc: usize,

    search_m: Function,
    search_b: Function,

    goal_pattern: Pattern<Lang>,
    new_goal_pattern: Pattern<Lang>,
}

#[derive(Debug, Clone)]
struct SubstData {
    search_m: Function,
    search_b: Function,
    new_term: Id,
}

impl SubstRule {
    pub fn new(
        DDH {
            subst,
            index,
            search_b,
            search_m,
            ..
        }: &DDH,
    ) -> Self {
        let g_pattern = Pattern::from(&rexp!((subst #SIDE #U #V #T #PROOF #B)));
        let ng_pattern = Pattern::from(&rexp!((EQUIV_WITH_SIDE #SIDE #U #V #NT #B)));

        Self {
            aenc: *index,
            goal_pattern: g_pattern,
            new_goal_pattern: ng_pattern,
            search_b: search_b.clone(),
            search_m: search_m.clone(),
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for SubstRule {
    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("subst aenc")
    }

    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> golgge::Dependancy {
        assert!(prgm.egraph().clean);
        ereturn_let!(let Some(matches) = self.goal_pattern.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        matches
            .substs
            .into_iter()
            .map(|mut subst| {
                let [nt_id, proof_id] = [T, PROOF].map(|v| *subst.get(v.as_egg()).unwrap());
                trace!("rebuilding in ddh");
                let na = (SubstData {
                    search_b: self.search_b.clone(),
                    search_m: self.search_m.clone(),
                    new_term: nt_id,
                })
                .proof_to_term(prgm, proof_id)
                .unwrap();
                subst.insert(NT.as_egg(), na);
                [self.new_goal_pattern.apply_susbt(prgm.egraph_mut(), &subst)]
            })
            .collect()
    }
}

impl ProofSubstitution for SubstData {
    type Proof = ProofHints;

    fn get_term<'a>(&self, pgrm: &mut CVProgram<'a>, id: Id) -> anyhow::Result<Id> {
        trace!("get term ({id:})");
        let l = pgrm.egraph()[id]
            .nodes
            .iter()
            .find(|Lang { head, .. }| head == &self.search_m || head == &self.search_b)
            .with_context(|| "not a proof of the expected form")?;
        Ok(l.args[3])
    }

    fn instance<'a>(&self, psargs: PSArgs<'_, 'a, Self>) -> anyhow::Result<Id> {
        trace!("instance: {psargs:#?}");
        Ok(self.new_term)
    }

    fn others<'a>(&self, _: PSArgs<'_, 'a, Self>) -> anyhow::Result<Id> {
        unreachable!()
    }
}

impl ProofLike<SubstData> for ProofHints {
    fn split<'pbl>(
        &self,
        prgrm: &mut CVProgram<'pbl>,
        data: &SubstData,
        proof_id: Id,
        proof_parent: &[Id],
        rule: &dyn CVRuleTrait<'pbl>,
    ) -> anyhow::Result<Id> {
        trace!("using prooghint:\n{self:#?}");
        let psargs = PSArgs {
            prgrm,
            proof_id,
            proof_parent,
            rule,
            proof: self,
        };
        match self {
            ProofHints::Keep => data.keep(psargs),
            ProofHints::Replace => data.instance(psargs),
            ProofHints::Apply(fun) => data.function_application(fun, psargs), /* _ => data.others(psarg), */
        }
    }
}
