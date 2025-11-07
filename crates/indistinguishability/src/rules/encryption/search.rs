use golgge::PrologRule;
use itertools::chain;

use crate::{
    Lang,
    problem::RcRule,
    rules::{AEnc, encryption::vars::*},
    terms::{
        AND, BITE, IS_FRESH_NONCE, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MITE, NONCE, PRED, VAMPIRE,
    },
};

fn mk_special_rules(
    AEnc {
        enc,
        dec,
        pk,
        search_k_b,
        search_k_m,
        search_o_b,
        search_o_m,
        search_k_trigger,
        search_o_pre_trigger,
        search_o_trigger,
        ..
    }: &AEnc,
) -> impl Iterator<Item = PrologRule<Lang>> {
    use super::ProofHints::*;
    // (search_o_m #K #K2 #R #T #H)
    // (search_k_m #K #T #H)
    chain![
        [
            mk_prolog! {
              "search_k_enc_key"; (Keep):
              (search_k_m #K (NONCE #K) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_key"; (Keep):
              (search_o_m #K #K2 #R (NONCE #K) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_rand"; (Keep):
              (search_o_m #K #K2 #R (NONCE #R) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_key2"; (Keep):
              (search_o_m #K #K2 #R (NONCE #K2) #H) :-!, (VAMPIRE (not #H))
            },
        ],
        mk_many_prolog! {
          "search_k_m_enc_false" (Keep):
            (search_k_m #K #T false).

          "search_k_b_enc_false" (Keep):
            (search_k_b #K #T false).

          "search_o_m_enc_false" (Keep):
            (search_o_m #K #K2 #R #M #T false).

          "search_o_b_enc_false" (Keep):
            (search_o_b #K #K2 #R #M #T false).

          "search_k_enc_nonce" (Keep):
            (search_k_m #K (NONCE #N) #H) :-
              (VAMPIRE (=> #H (distinct #K #N))).

          "search_o_enc_nonce" (Keep):
            (search_k_m #K #K2 #R #M (NONCE #N) #H) :-
              (VAMPIRE (=> #H (distinct #K #N))),
              (VAMPIRE (=> #H (distinct #K2 #N))),
              (VAMPIRE (=> #H (distinct #R #N))).

          "search_o_indtance" (Replace):
            (search_o_m #K #K2 #R #M (enc #M (NONCE #R) (pk (NONCE #K))) #H).
        },
        //
        mk_many_prolog! {
          "search_k_enc_pk" (Apply(pk.clone())):
            (search_k_m #K (pk (NONCE #N)) #H).

          "search_o_enc_pk" (Apply(pk.clone())):
            (search_k_m #K #K2 #R #M (pk (NONCE #N)) #H).

          "search_k_enc_dec" (Apply(dec.clone())):
            (search_k_m #K (dec #A #B) #H):-
              (search_k_m #K #A #H),
              (search_k_m #K #B #H).

          "search_o_enc_dec" (Apply(dec.clone())):
            (search_o_m #K #K2 #R #M (dec #A #B) #H) :-
              (search_o_m #K #K2 #R #M #A #H).

            // macros
            "search_k_enc_exec"  (Keep):
            (search_k_b #K (MACRO_EXEC #T  #P) #H) :-
            (search_k_trigger #K #T #P #H).

            "search_o_enc_exec"  (Keep):
            (search_k_b #K #K2 #R (MACRO_EXEC #T  #P) #H) :-
            (search_o_pre_trigger #K #K2 #R #T #P #H).

            "search_k_enc_frame"  (Keep):
            (search_k_m #K (MACRO_FRAME #T  #P) #H) :-
            (search_k_trigger #K #K2 #T #P #H).

            "search_o_enc_frame" (Keep):
            (search_k_b #K #K2 #R (MACRO_FRAME #T  #P) #H) :-
            (search_o_pre_trigger #K #K2 #R #T #P #H).

            "search_k_enc_input" (Keep):
            (search_k_m #K (MACRO_INPUT #T  #P) #H) :-
            (search_k_trigger #K (PRED #T) #P #H).

            "search_o_enc_input" (Keep):
            (search_k_b #K #K2 #R (MACRO_INPUT #T  #P) #H) :-
            (search_o_pre_trigger #K #K2 #R (PRED #T) #P #H).

            // trigger
            "search_o_ind_cca_trigger" :
              (search_o_pre_trigger #K #K #R #T #P #H) :-
                (search_o_trigger #K #R #T #P #H).

            "search_o_enc_kp_trigger" :
              (search_o_pre_trigger #K (IS_FRESH_NONCE #K2) #R #T #P #H) :-
                (search_o_trigger #K #R #T #P #H).

            "search_k_enc_trigger_skip":
              (search_k_trigger (IS_FRESH_NONCE #K) #T #P #H).

            // if and and
            "search_enc_ite_m" c, l, r (Apply(MITE.clone())):
            (search_k_m #K (MITE #c #l #r) #H):-
                (search_k_b #K #c #H),
                (search_k_m #K #l (and #c #H)),
                (search_k_m #K #r (and (not #c) #H)).

            "search_o_enc_ite_m" c, l, r (Apply(MITE.clone())):
            (search_o_m #K #K2 #R (MITE #c #l #r) #H):-
                (search_o_b #K #K2 #R #c #H),
                (search_o_m #K #K2 #R #l (and #c #H)),
                (search_o_m #K #K2 #R #r (and (not #c) #H)).

            "search_enc_ite_b" c, l, r (Apply(MITE.clone())):
            (search_k_b #K (BITE #c #l #r) #H):-
                (search_k_b #K #c #H),
                (search_k_b #K #l (and #c #H)),
                (search_k_b #K #r (and (not #c) #H)).

            "search_o_enc_ite_m" c, l, r (Apply(BITE.clone())):
            (search_o_b #K #K2 #R (BITE #c #l #r) #H):-
                (search_o_b #K #K2 #R #c #H),
                (search_o_b #K #K2 #R #l (and #c #H)),
                (search_o_b #K #K2 #R #r (and (not #c) #H)).

            "search_encand" c, l, r (Apply(AND.clone())):
            (search_k_b #K (AND #c #l) #H):-
                (search_k_b #K #c #H),
                (search_k_b #K #r (and  #c #H)).

            "search_o_enc_ite_m" c, l (Apply(AND.clone())):
            (search_o_b #K #K2 #R (AND #c #l) #H):-
                (search_o_b #K #K2 #R #c #H),
                (search_o_b #K #K2 #R #l (and #c #H)).
        }
    ]
}
