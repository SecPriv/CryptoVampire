use std::fmt::Debug;

use anyhow::{Context, Result, ensure};
use egg::Id;
use golgge::{Program, ProofItem};
use itertools::Itertools;
use log::trace;

use crate::problem::{CVRuleTrait, PAnalysis, RcRule};
use crate::terms::{Function, Sort};
use crate::{CVProgram, Lang};

pub trait ProofLike<S: ProofSubstitution + ?Sized> {
    fn split<'pbl>(
        &self,
        prgrm: &mut Program<Lang, PAnalysis<'pbl>, RcRule>,
        data: &S,
        proof_id: Id,
        parent: &[Id],
        rule: &dyn CVRuleTrait<'pbl>,
    ) -> Result<Id>;
}

pub struct PSArgs<'a, 'pbl, S: ProofSubstitution + ?Sized> {
    pub prgrm: &'a mut CVProgram<'pbl>,
    pub proof: &'a S::Proof,
    pub proof_id: Id,
    pub proof_parent: &'a [Id],
    pub rule: &'a dyn CVRuleTrait<'pbl>,
}

pub trait ProofSubstitution {
    type Proof: ProofLike<Self> + 'static;

    fn proof_to_term<'a>(&self, pgrm: &mut CVProgram<'a>, proof: Id) -> Result<Id> {
        trace!(
            "proof to term from ({proof:}):\n\t{}",
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
            "(prf) substitution from rule:\n\t{rule:?}",
            /* golgge::DebugRule::new(rule.as_ref()) */
        );

        prf_proof.split(pgrm, self, proof, &ids, rule.as_ref())
    }

    /// retrieves the term to apply substitution to from a proo
    fn get_term<'a>(&self, prgrm: &mut CVProgram<'a>, proof: Id) -> Result<Id>;

    /// when the proof ask to "keep" the term
    fn keep<'a>(
        &self,
        PSArgs {
            prgrm, proof_id, ..
        }: PSArgs<'_, 'a, Self>,
    ) -> Result<Id> {
        trace!("keep term");
        self.get_term(prgrm, proof_id)
    }

    /// when the proffs ask to apply an instance
    fn instance<'a>(&self, args: PSArgs<'_, 'a, Self>) -> Result<Id>;

    fn function_application<'a>(&self, fun: &Function, psargs: PSArgs<'_, 'a, Self>) -> Result<Id> {
        trace!("rebuilding proof with {fun}:\n{psargs:#?}");
        let PSArgs {
            prgrm,
            proof_id,
            proof_parent: ids,
            ..
        } = psargs;

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
        let args: Result<_> = fun
            .args_sorts()
            .zip_eq(old_args)
            .map(|(s, bid)| {
                trace!("{s}: {:}", usize::from(bid));
                if s == Sort::Bool || s == Sort::Bitstring {
                    trace!("recurse rebuilding");
                    self.proof_to_term(
                        prgrm,
                        *args_proofs.next().with_context(|| "no enough arguments")?,
                    )
                } else {
                    trace!("skip");
                    Ok(bid)
                }
            })
            .collect();
        let args = args?;

        ensure!(args_proofs.next().is_none(), "too many arguements");
        Ok(prgrm.egraph_mut().add(Lang {
            head: fun.clone(),
            args,
        }))
    }

    fn others<'a>(&self, args: PSArgs<'_, 'a, Self>) -> Result<Id>;
}

impl<'a, 'pbl, S: ProofSubstitution + ?Sized> Debug for PSArgs<'a, 'pbl, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PSArgs")
            .field("proof_parent_ids", &self.proof_parent)
            .field("rule", &self.rule.name())
            .field("proof_id", &self.proof_id)
            .field(
                "proof",
                &self.prgrm.egraph().id_to_expr(self.proof_id).pretty(100),
            )
            .finish()
    }
}
