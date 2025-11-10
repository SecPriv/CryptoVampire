use egg::Id;
use golgge::{Program, ProofItem, Rule};
use itertools::izip;
use log::trace;

use crate::{
    Lang,
    problem::PAnalysis,
    terms::{Function, Sort},
};

pub trait ProofLike<S: ProofSubstitution + ?Sized> {
    fn split<'pbl>(
        &self,
        prgrm: &mut Program<Lang, PAnalysis<'pbl>>,
        data: &S,
        proof_id: Id,
        parent: &[Id],
        rule: &dyn Rule<Lang, PAnalysis<'pbl>>,
    ) -> Result<Id>;
}

pub struct PSArgs<'a, 'pbl, S: ProofSubstitution + ?Sized> {
    pub prgrm: &'a mut Program<Lang, PAnalysis<'pbl>>,
    pub proof: &'a S::Proof,
    pub proof_id: Id,
    pub proof_parent: &'a [Id],
    pub rule: &'a dyn Rule<Lang, PAnalysis<'pbl>>,
}

use anyhow::{Context, Result, ensure};

pub trait ProofSubstitution {
    type Proof: ProofLike<Self> + 'static;

    fn proof_to_term<'a>(&self, pgrm: &mut Program<Lang, PAnalysis<'a>>, proof: Id) -> Result<Id> {
        trace!(
            "proof to term from:\n\t{}",
            pgrm.egraph().id_to_expr(proof).pretty(100)
        );
        let ProofItem { ids, payload, rule } =
            pgrm.get_proof_item(proof).with_context(|| "no proof")?;
        let prf_proof: Option<&Self::Proof> = payload
            .as_ref()
            .with_context(|| "no proof object")?
            .downcast_ref();
        let prf_proof = prf_proof.with_context(|| "can't convert proof type")?;
        trace!(
            "(prf) substitution from rule:\n\t{:?}",
            golgge::DebugRule::new(rule.as_ref())
        );

        prf_proof.split(pgrm, &self, proof, &ids, rule.as_ref())
    }

    /// retrieves the term to apply substitution to from a proo
    fn get_term<'a>(&self, prgrm: &mut Program<Lang, PAnalysis<'a>>, proof: Id) -> Result<Id>;

    /// when the proof ask to "keep" the term
    fn keep<'a>(
        &self,
        PSArgs {
            prgrm, proof_id, ..
        }: PSArgs<'_, 'a, Self>,
    ) -> Result<Id> {
        self.get_term(prgrm, proof_id)
    }

    /// when the proffs ask to apply an instance
    fn instance<'a>(&self, args: PSArgs<'_, 'a, Self>) -> Result<Id>;

    fn function_application<'a>(
        &self,
        fun: &Function,
        PSArgs {
            prgrm,
            proof_id,
            proof_parent: ids,
            ..
        }: PSArgs<'_, 'a, Self>,
    ) -> Result<Id> {
        let t = self.get_term(prgrm, proof_id)?;
        let mut args_proofs = ids.iter();
        let old_args = prgrm.egraph()[t]
            .nodes
            .iter()
            .find(|l| &l.head == fun)
            .with_context(|| format!("{fun} is not a constructor"))?
            .args
            .clone();

        // collect the arguments, mixing the old and the new depending
        // on their sort. Irrelevant sorts don't have proofs.
        let args: Result<_> = izip!(fun.args_sorts(), old_args)
            .map(|(s, bid)| {
                if s == Sort::Bool || s == Sort::Bitstring {
                    self.proof_to_term(
                        prgrm,
                        *args_proofs.next().with_context(|| "no enough arguements")?,
                    )
                } else {
                    Ok(bid)
                }
            })
            .collect();

        ensure!(args_proofs.next().is_none(), "too many arguements");
        Ok(prgrm.egraph_mut().add(Lang {
            head: fun.clone(),
            args: args?,
        }))
    }

    fn others<'a>(&self, args: PSArgs<'_, 'a, Self>) -> Result<Id>;
}
