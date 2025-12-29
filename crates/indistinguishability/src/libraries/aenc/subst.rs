use anyhow::Context;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use utils::ereturn_let;

use super::vars::*;
use crate::libraries::AEnc;
use crate::libraries::aenc::ProofHints;
use crate::libraries::substitution::{PSArgs, ProofLike, ProofSubstitution};
use crate::libraries::utils::TwoSortFunction;
use crate::problem::{CVRuleTrait, PAnalysis, PRule, RcRule};
use crate::terms::{EQUIV_WITH_SIDE, Function};
use crate::{CVProgram, Lang, Problem, rexp};

pub fn mk_rules(_: &Problem, aenc: &AEnc) -> impl Iterator<Item = RcRule> {
    [SubstRule::new(aenc).into_mrc()].into_iter()
}

#[derive(Debug, Clone)]
struct SubstRule {
    #[allow(dead_code)]
    aenc: usize,

    goal_pattern: Pattern<Lang>,
    new_goal_pattern: Pattern<Lang>,

    pk: Option<Function>,
    dec: Function,
    search: TwoSortFunction,
}

#[derive(Debug, Clone)]
struct SubstData {
    new_term: Id,
    search: TwoSortFunction,
    pk: Option<Function>,
    dec: Function,
}

impl SubstRule {
    pub fn new(
        AEnc {
            subst,
            index,
            dec,
            pk,
            search_k,
            ..
        }: &AEnc,
    ) -> Self {
        let g_pattern = Pattern::from(&rexp!((subst #SIDE #U #V #T #PROOF #B)));
        let ng_pattern = Pattern::from(&rexp!((EQUIV_WITH_SIDE #SIDE #U #V #NT #B)));

        Self {
            aenc: *index,
            goal_pattern: g_pattern,
            new_goal_pattern: ng_pattern,
            pk: pk.clone(),
            dec: dec.clone(),
            search: search_k.clone(),
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for SubstRule {
    fn name(&self) -> std::borrow::Cow<'_, str> {
        std::borrow::Cow::Borrowed("subst aenc")
    }

    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> golgge::Dependancy {
        ereturn_let!(let Some(matches) = self.goal_pattern.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        matches
            .substs
            .into_iter()
            .map(|mut subst| {
                let [nt_id, proof_id] = [T, PROOF].map(|v| *subst.get(v.as_egg()).unwrap());
                let na = (SubstData {
                    new_term: nt_id,
                    pk: self.pk.clone(),
                    dec: self.dec.clone(),
                    search: self.search.clone(),
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
        let l = pgrm.egraph()[id]
            .nodes
            .iter()
            .find(|Lang { head, .. }| self.search.contains(head))
            .with_context(|| "not a proof of the expected form")?;
        Ok(l.args[4])
    }

    fn instance<'a>(&self, _: PSArgs<'_, 'a, Self>) -> anyhow::Result<Id> {
        Ok(self.new_term)
    }

    fn others<'a>(&self, args: PSArgs<'_, 'a, Self>) -> anyhow::Result<Id> {
        let PSArgs {
            proof,
            proof_parent,
            prgrm,
            proof_id,
            ..
        } = args;
        match proof {
            // search_k_enc_fa_m_weak case: keep `A` reconstruct `B`
            ProofHints::FaKeep(f) => {
                let self_id = self.get_term(prgrm, proof_id)?;

                let b = proof_parent
                    .iter()
                    .cloned()
                    .next()
                    .with_context(|| "wrong number of argument in fa (needs at least 1)")?;
                let nb = self.proof_to_term(prgrm, b)?;
                let na = prgrm.egraph()[self_id]
                    .nodes
                    .iter()
                    .find_map(|Lang { head, args }| (head == f).then(|| args[0]))
                    .with_context(|| "not a fa")?;
                Ok(prgrm.egraph_mut().add(f.app_id([na, nb])))
            }

            ProofHints::Apply(fun) => {
                if fun == &self.dec {
                    if proof_parent.len() == 2 {
                        self.function_application(&self.dec, PSArgs { prgrm, ..args })
                    } else {
                        todo!()
                    }
                } else if Some(fun) == self.pk.as_ref() {
                    todo!()
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        }
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
            ProofHints::Apply(fun) if Some(fun) != data.pk.as_ref() && fun != &data.dec => {
                // NB: enc is a behaves like a regular function
                data.function_application(fun, psargs)
            }
            _ => data.others(psargs),
        }
    }
}
