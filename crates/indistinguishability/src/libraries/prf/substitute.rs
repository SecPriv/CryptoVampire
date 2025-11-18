use std::borrow::Cow;

use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Program, ProofItem, Rule};
use itertools::izip;
use utils::ereturn_let;

use crate::{
    Lang,
    problem::PAnalysis,
    libraries::{
        PRF,
        prf::{K, M, NEW_TERM, NK, PRFProof, PROOF},
    },
    terms::{CryptographicAssumption, Function, NONCE, Sort},
};

#[derive(Debug, Clone, Builder)]
pub struct SubstRule {
    #[builder(into)]
    pub trigger: Pattern<Lang>,
    #[builder(into)]
    pub new_goal: Pattern<Lang>,
    pub prf_idx: usize,
}

#[derive(Debug, Clone)]
struct SubstData {
    m: Id,
    k: Id,
    nprf: Id,

    hash: Function,
    search_bitstring: Function,
    search_bool: Function,
}

impl SubstData {
    fn proof_to_term<'a>(&self, pgrm: &mut Program<Lang, PAnalysis<'a>>, proof: Id) -> Id {
        tr!(
            "proof to term from:\n\t{}",
            pgrm.egraph().id_to_expr(proof).pretty(100)
        );
        let ProofItem { ids, payload, rule } = pgrm.get_proof_item(proof).unwrap();
        let prf_proof = payload.as_ref().unwrap().downcast_ref().unwrap();
        tr!(
            "(prf) substitution from rule:\n\t{:?}",
            golgge::DebugRule::new(rule.as_ref())
        );

        match prf_proof {
            PRFProof::Keep => self.get_term(pgrm, proof),
            PRFProof::Instance => pgrm.egraph_mut().add(NONCE.app_id([self.nprf])),
            PRFProof::Apply(f) if f != &self.hash => {
                let t = self.get_term(pgrm, proof);
                let mut args_proofs = ids.into_iter();
                let old_args = pgrm.egraph()[t]
                    .nodes
                    .iter()
                    .find(|l| &l.head == f)
                    .unwrap()
                    .args
                    .clone();

                // collect the arguments, mixing the old and the new depending
                // on their sort. Irrelevant sorts don't have proofs.
                let args = izip!(f.signature.inputs.iter(), old_args)
                    .map(|(&s, bid)| {
                        if s == Sort::Bool || s == Sort::Bitstring {
                            self.proof_to_term(pgrm, args_proofs.next().unwrap())
                        } else {
                            bid
                        }
                    })
                    .collect();

                assert!(args_proofs.next().is_none());
                pgrm.egraph_mut().add(Lang {
                    head: f.clone(),
                    args,
                })
            }
            PRFProof::Apply(f) => {
                assert_eq!(f, &self.hash);
                match ids.len() {
                    2 => {
                        // neq m
                        let m = self.proof_to_term(pgrm, ids[1]);
                        let egraph = pgrm.egraph_mut();
                        let nk = egraph.add(NONCE.app_id([self.k]));
                        egraph.add(f.app_id([m, nk]))
                    }
                    4 => {
                        // neq k
                        // we need to skip 2 vampire proofs
                        let args = ids[2..]
                            .iter()
                            .map(|&proof| self.proof_to_term(pgrm, proof))
                            .collect();
                        pgrm.egraph_mut().add(Lang {
                            head: f.clone(),
                            args,
                        })
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn get_term<'a>(&self, pgrm: &Program<Lang, PAnalysis<'a>>, id: Id) -> Id {
        let Self {
            search_bitstring,
            search_bool,
            ..
        } = self;

        tr!(
            "(prf) substitution: get_term\n\t{}",
            pgrm.egraph().id_to_expr(id).pretty(100)
        );
        let l = pgrm.egraph()[id]
            .nodes
            .iter()
            .find(|Lang { head, args }| {
                (head == search_bitstring || head == search_bool)
                    && args[0] == self.m
                    && args[1] == self.k
                    && args[2] == self.nprf
            })
            .unwrap();
        l.args[3]
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>> for SubstRule {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("prf substitution")
    }

    fn search(&self, prgm: &mut Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        ereturn_let!(let Some(substs)= self.trigger.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        let CryptographicAssumption::PRF(PRF {
            hash,
            search_bitstring,
            search_bool,
            ..
        }) = &prgm.egraph().analysis.pbl().cryptography()[self.prf_idx]
        else {
            unreachable!()
        };
        let hash = hash.clone();
        let search_bitstring = search_bitstring.clone();
        let search_bool = search_bool.clone();

        let mut ret = Vec::with_capacity(substs.substs.len());
        for mut subst in substs.substs {
            let [m, k, nprf, proof] = [M, K, NK, PROOF].map(|v| *subst.get(v.as_egg()).unwrap());

            let nt = SubstData {
                m,
                k,
                nprf,
                hash: hash.clone(),
                search_bitstring: search_bitstring.clone(),
                search_bool: search_bool.clone(),
            }
            .proof_to_term(prgm, proof);

            subst.insert(NEW_TERM.as_egg(), nt);

            ret.push([self.new_goal.apply_susbt(prgm.egraph_mut(), &subst)]);
        }
        ret.into_iter().collect()
    }
}
