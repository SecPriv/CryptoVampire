use utils::dynamic_iter;

use super::vars::*;
use crate::Problem;
use crate::libraries::AEnc;
use crate::libraries::utils::TwoSortFunction;
use crate::problem::{PRule, RcRule};
use crate::terms::{EQUIV, FRESH_NONCE, LEFT, LENGTH, NONCE, RIGHT, ZEROES};

pub fn mk_rules(
    _: &Problem,
    AEnc {
        enc,
        subst,
        pk,
        candidate: TwoSortFunction { m: candidate, .. },
        search_o: TwoSortFunction { m: search_o, .. },
        search_k: TwoSortFunction { m: search_k, .. },
        ..
    }: &AEnc,
) -> impl Iterator<Item = RcRule> {
    dynamic_iter!(MIter; A:A, B:B);

    if let Some(pk) = pk {
        let ret = mk_many_prolog! {
          "ind-cca1-left" :
            (EQUIV #U #V (candidate #T #M #R #K) #B) :-
              (search_o #K #M true),
              (FRESH_NONCE #R #M true),
              (search_k #K #K #R #M #T true),
              (subst LEFT #U #V
                (enc (ZEROES (LENGTH #M)) (NONCE #R) (pk (NONCE #K))) (search_k #K #K #R #M #T true)
                #B).

          "ind-cca1-right" :
            (EQUIV #U #V #B (candidate #T #M #R #K)) :-
              (search_o #K #M true),
              (FRESH_NONCE #R #M true),
              (search_k #K #K #R #M #T true),
              (subst RIGHT #U #V
                (enc (ZEROES (LENGTH #M)) (NONCE #R) (pk (NONCE #K))) (search_k #K #K #R #M #T true)
                #B).
        }
        .into_iter()
        .map(|x| x.into_mrc());
        MIter::A(ret)
    } else {
        // no ind-cca if senc
        MIter::B(::std::iter::empty())
    }
}
