use itertools::chain;

use crate::problem::{PRule, RcRule};
use crate::rules::deduce::GetDeduce;
use crate::terms::{
    AND, BIT_DEDUCE, BITE, BOOL_DEDUCE, EQUIV, FAIL, FRESH_NONCE, HAPPENS, IS_FRESH_NONCE, LEQ,
    MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, MITE, NONCE, VAMPIRE,
};

/// Creates a set of static deduction rules.
pub fn mk_rules() -> impl Iterator<Item = RcRule> {
    let equiv = &EQUIV;
    let deduce_m = &BIT_DEDUCE;
    let deduce_b = &BOOL_DEDUCE;
    let b_ite = &BITE;
    let m_ite = &MITE;
    decl_vars![t, t2, p1, p2, h1, h2, u, v, a, b, a1, b1, a2, b2, c1, c2, x];

    let deduce_macro = [
        &MACRO_FRAME,
        &MACRO_EXEC,
        &MACRO_COND,
        &MACRO_INPUT,
        &MACRO_MSG,
    ]
    .map(|mmacro| {
        let deduce = mmacro.get_deduce();
        mk_prolog!(
          format!("deduce {mmacro}"); :
          (deduce (MACRO_FRAME #t #p1) (MACRO_FRAME #t #p2) (mmacro #t2 #p1) (mmacro #t2 #p2) #h1 #h2) :-
            (VAMPIRE (=> #h1 (LEQ #t2 #t))),
            (VAMPIRE (=> #h2 (LEQ #t2 #t))),
            (VAMPIRE (HAPPENS #t))
        )
    });

    let vampire_fail = mk_prolog!("vampire false";: (VAMPIRE false) :-!,FAIL);

    let others = mk_many_prolog! {
        "vampire trivial":
        (VAMPIRE true).

        "equiv axiom":
        (equiv #u #v #x #x).

        "equiv deduce":
        (equiv #u #v #a #b) :-
          (deduce_m #u #v #a #b true true).

        "deduce m trivial":
        (deduce_m #u #v #a #b false false).

        "deduce b trivial":
        (deduce_b #u #v #a #b false false).

    // =========================================================
    // ========================= ite ===========================
    // =========================================================

        // "deduce b_ite":
        // (deduce_b #u #v (b_ite #a1 #b1 #c1) (b_ite #a2 #b2 #c2) #h1 #h2) :-
        //   (deduce_b #u #v #b1 #b2 (and #a1 #h1) (and #a2 #h2)),
        //   (deduce_b #u #v #c1 #c2 (and (not #a1) #h1) (and (not #a2) #h2)),
        //   (deduce_b #u #v #a1 #a2 #h1 #h2).

        "deduce m_ite":
        (deduce_m #u #v (m_ite #a1 #b1 #c1) (m_ite #a2 #b2 #c2) #h1 #h2) :-
          (deduce_m #u #v #b1 #b2 (and #a1 #h1) (and #a2 #h2)),
          (deduce_m #u #v #c1 #c2 (and (not #a1) #h1) (and (not #a2) #h2)),
          (deduce_b #u #v #a1 #a2 #h1 #h2).

        "deduce mand":
        (deduce_b #u #v (AND #a1 #b1) (AND #a2 #b2) #h1 #h2) :-
          (deduce_b #u #v #a1 #a2 #h1 #h2),
          (deduce_b #u #v #b1 #b2 (and #h1 #a1) (and #h2 #a2)).

    // =========================================================
    // ======================== other ==========================
    // =========================================================

        "deduce fresh nonces":
        (deduce_m #u #v (NONCE #x) (NONCE #x) #h1 #h2):-
          (FRESH_NONCE #x #u #h1),
          (FRESH_NONCE #x #v #h2).

        "fresh nonce fresh":
        (FRESH_NONCE (IS_FRESH_NONCE #x) #u #h1).
    };

    chain![deduce_macro, [vampire_fail], others].map(|x| x.into_mrc())
}
