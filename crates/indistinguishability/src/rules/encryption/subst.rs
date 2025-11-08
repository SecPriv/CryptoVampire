use anyhow::Context;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Program, Rule};
use itertools::Itertools;
use utils::ereturn_let;

use crate::{
    Lang,
    problem::PAnalysis,
    rexp,
    rules::{
        AEnc,
        encryption::ProofHints,
        substitution::{PSArgs, ProofLike, ProofSubstitution},
    },
    terms::{EQUIV_WITH_SIDE, Function},
};

use super::vars::*;

#[derive(Debug, Clone)]
pub struct SubstRule {
    aenc: usize,

    search_o_m: Function,
    search_o_b: Function,

    goal_pattern: Pattern<Lang>,
    new_goal_pattern: Pattern<Lang>,
}

#[derive(Debug, Clone)]
struct SubstData {
    search_o_m: Function,
    search_o_b: Function,
    new_term: Id,
}

impl SubstRule {
    pub fn new(
        AEnc {
            subst,
            index,
            search_o_b,
            search_o_m,
            ..
        }: &AEnc,
    ) -> Self {
        let g_pattern = Pattern::from(&rexp!((subst #SIDE #U #V #T #PROOF #B)));
        let ng_pattern = Pattern::from(&rexp!((EQUIV_WITH_SIDE #SIDE #U #V #NT #B)));

        Self {
            aenc: *index,
            goal_pattern: g_pattern,
            new_goal_pattern: ng_pattern,
            search_o_b: search_o_b.clone(),
            search_o_m: search_o_m.clone(),
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>> for SubstRule {
    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("subst aenc")
    }

    fn search(&self, prgm: &mut Program<Lang, PAnalysis<'a>>, goal: Id) -> golgge::Dependancy {
        ereturn_let!(let Some(matches) = self.goal_pattern.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        matches
            .substs
            .into_iter()
            .map(|mut subst| {
                let [nt_id, proof_id] = [T, PROOF].map(|v| *subst.get(v.as_egg()).unwrap());
                let na = (SubstData {
                    search_o_b: self.search_o_b.clone(),
                    search_o_m: self.search_o_m.clone(),
                    new_term: nt_id,
                })
                .get_term(prgm, proof_id)
                .unwrap();
                subst.insert(NT.as_egg(), na);
                [self.new_goal_pattern.apply_susbt(prgm.egraph_mut(), &subst)]
            })
            .collect()
    }
}

impl ProofSubstitution for SubstData {
    type Proof = ProofHints;

    fn get_term<'a>(&self, pgrm: &mut Program<Lang, PAnalysis<'a>>, id: Id) -> anyhow::Result<Id> {
        let l = pgrm.egraph()[id]
            .nodes
            .iter()
            .find(|Lang { head, .. }| head == &self.search_o_m || head == &self.search_o_b)
            .with_context(|| "not a proof of the expected form")?;
        Ok(l.args[3])
    }

    fn instance<'a>(&self, _: PSArgs<'_, 'a, Self>) -> anyhow::Result<Id> {
        Ok(self.new_term)
    }

    fn others<'a>(
        &self,
        PSArgs {
            proof,
            proof_parent,
            prgrm,
            proof_id,
            ..
        }: PSArgs<'_, 'a, Self>,
    ) -> anyhow::Result<Id> {
        let ProofHints::FaKeep(f) = proof else {
            unreachable!()
        };
        let self_id = self.get_term(prgrm, proof_id)?;

        let (_, b) = proof_parent
            .iter()
            .cloned()
            .collect_tuple()
            .with_context(|| "wrong number of argument in fa")?;
        let nb = self.proof_to_term(prgrm, b)?;
        let na = prgrm.egraph()[self_id]
            .nodes
            .iter()
            .find_map(|Lang { head, args }| (head == f).then(|| args[0]))
            .with_context(|| "not a fa")?;
        Ok(prgrm.egraph_mut().add(f.app_id([na, nb])))
    }
}

impl ProofLike<SubstData> for ProofHints {
    fn split<'pbl>(
        &self,
        prgrm: &mut Program<Lang, PAnalysis<'pbl>>,
        data: &SubstData,
        proof_id: Id,
        proof_parent: &[Id],
        rule: &dyn golgge::Rule<Lang, PAnalysis<'pbl>>,
    ) -> anyhow::Result<Id> {
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
            ProofHints::Apply(fun) => data.function_application(fun, psargs),
            _ => data.others(psargs),
        }
    }
}
