use super::vars::*;
use crate::{
    Problem,
    problem::{PRule, RcRule},
    terms::{EQUIV, FRESH_NONCE, LEFT, LENGTH, NONCE, RIGHT, ZEROES},
};
use super::{XOr, ProofHints, vars::*};

pub fn mk_rules(
    _: &Problem,
    XOr {
        candidate_m,
        enc,
        search_o_m,
        search_k_m,
        subst,
        pk, 
        ..
    }: &XOr,
) -> impl Iterator<Item = RcRule> {
    mk_many_prolog! {
      "ind-ccsa left" :
        (EQUIV #U #V (candidate_m #T #M #R #K) #B) :-
          (search_k_m #K #M true),
          (FRESH_NONCE #R #M true),
          (search_o_m #K #K #R #M #T true),
          (subst LEFT #U #V
            (enc (ZEROES (LENGTH #M)) (NONCE #R) (pk (NONCE #K))) (search_o_m #K #K #R #M #T true)
            #B).

      "ind-ccsa left" :
        (EQUIV #U #V #B (candidate_m #T #M #R #K)) :-
          (search_k_m #K #M true),
          (FRESH_NONCE #R #M true),
          (search_o_m #K #K #R #M #T true),
          (subst RIGHT #U #V
            (enc (ZEROES (LENGTH #M)) (NONCE #R) (pk (NONCE #K))) (search_o_m #K #K #R #M #T true)
            #B).
    }
    .into_iter()
    .map(|x| x.into_mrc())
}
