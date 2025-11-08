use egg::Pattern;
use golgge::PrologRule;
use itertools::{Itertools, chain, izip};

use crate::{
    Lang, Problem, fresh, rexp,
    rules::{
        AEnc,
        aenc::{ProofHints, vars::*},
    },
    terms::{
        AND, BITE, CONS_FA_BITSTRING, CONS_FA_BOOL, FRESH_NONCE, Function, IS_FRESH_NONCE,
        MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MITE, NONCE, PRED, RecFOFormula, Sort, VAMPIRE,
    },
};

pub fn mk_static_rules<'a>(
    pbl: &'a Problem,
    aenc @ AEnc {
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
    }: &'a AEnc,
) -> impl Iterator<Item = PrologRule<Lang>> + use<'a> {
    let function_to_skip = [
        NONCE.clone(),
        dec.clone(),
        pk.clone(),
        AND.clone(),
        CONS_FA_BITSTRING.clone(),
        CONS_FA_BOOL.clone(),
    ];

    let functions = pbl
        .functions()
        .iter_current()
        .filter(move |f| !function_to_skip.contains(*f))
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm())
        .cloned();
    use super::super::ProofHints::*;
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
              (search_o_m #K #K2 #R #M (NONCE #K) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_rand"; (Keep):
              (search_o_m #K #K2 #R #M (NONCE #R) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_key2"; (Keep):
              (search_o_m #K #K2 #R #M (NONCE #K2) #H) :-!, (VAMPIRE (not #H))
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
            (search_o_m #K #K2 #R #M (NONCE #N) #H) :-
              (VAMPIRE (=> #H (distinct #K #N))),
              (VAMPIRE (=> #H (distinct #K2 #N))),
              (VAMPIRE (=> #H (distinct #R #N))).

          "search_o_indtance" (Replace):
            (search_o_m #K #K2 #R #M (enc #M (NONCE #R) (pk (NONCE #K))) #H).
        },
        functions.flat_map(|f| mk_rule_one(aenc, &f)),
        mk_many_prolog! {
          "search_k_enc_pk" (Keep):
            (search_k_m #K (pk (NONCE #K)) #H).
          
          "search_k_enc_pk_neq" (Keep):
            (search_k_m #K (pk #T) #H) :-
              (search_k_m #K #T #H),
              (VAMPIRE (=> #H (distinct #T (NONCE #K)))).

          "search_o_enc_pk" (Keep):
            (search_o_m #K #K2 #R #M (pk (NONCE #K)) #H).

          "search_o_enc_pk2" (Keep):
            (search_o_m #K #K2 #R #M (pk (NONCE #K2)) #H).

          "search_o_enc_pk2" (Keep):
            (search_o_m #K #K2 #R #M (pk (NONCE #K2)) #H).

          "search_k_enc_dec" (Apply(dec.clone())):
            (search_k_m #K (dec #A #B) #H):-
              (search_k_m #K #A #H),
              (search_k_m #K #B #H).

          "search_o_enc_dec" (Apply(dec.clone())):
            (search_o_m #K #K2 #R #M (dec #A #B) #H) :-
              (search_o_m #K #K2 #R #M #A #H),
              (search_o_m #K #K2 #R #M (pk #B) #H).

          // macros
          "search_k_enc_exec"  (Keep):
            (search_k_b #K (MACRO_EXEC #T  #P) #H) :-
              (search_k_trigger #K #T #P #H).

          "search_o_enc_exec"  (Keep):
            (search_o_b #K #K2 #R #M (MACRO_EXEC #T  #P) #H) :-
              (search_o_pre_trigger #K #K2 #R #T #P #H).

          "search_k_enc_frame"  (Keep):
            (search_k_m #K (MACRO_FRAME #T  #P) #H) :-
              (search_k_trigger #K #T #P #H).

          "search_o_enc_frame" (Keep):
            (search_o_m #K #K2 #R #M (MACRO_FRAME #T  #P) #H) :-
              (search_o_pre_trigger #K #K2 #R #T #P #H).

          "search_k_enc_input" (Keep):
            (search_k_m #K (MACRO_INPUT #T  #P) #H) :-
              (search_k_trigger #K (PRED #T) #P #H).

          "search_o_enc_input" (Keep):
            (search_o_m #K #K2 #R #M (MACRO_INPUT #T  #P) #H) :-
              (search_o_pre_trigger #K #K2 #R (PRED #T) #P #H).

          // if and and
          "search_enc_ite_m" c, l, r (Apply(MITE.clone())):
            (search_k_m #K (MITE #c #l #r) #H):-
              (search_k_b #K #c #H),
              (search_k_m #K #l (and #c #H)),
              (search_k_m #K #r (and (not #c) #H)).

          "search_o_enc_ite_m" c, l, r (Apply(MITE.clone())):
            (search_o_m #K #K2 #R #M (MITE #c #l #r) #H):-
              (search_o_b #K #K2 #R #M #c #H),
              (search_o_m #K #K2 #R #M #l (and #c #H)),
              (search_o_m #K #K2 #R #M #r (and (not #c) #H)).

          "search_k_enc_ite_b" c, l, r (Apply(BITE.clone())):
            (search_k_b #K (BITE #c #l #r) #H):-
              (search_k_b #K #c #H),
              (search_k_b #K #l (and #c #H)),
              (search_k_b #K #r (and (not #c) #H)).

          "search_o_enc_ite_m" c, l, r (Apply(BITE.clone())):
            (search_o_b #K #K2 #R #M (BITE #c #l #r) #H):-
              (search_o_b #K #K2 #R #M #c #H),
              (search_o_b #K #K2 #R #M #l (and #c #H)),
              (search_o_b #K #K2 #R #M #r (and (not #c) #H)).

          "search_enc_and" c, l (Apply(AND.clone())):
            (search_k_b #K (AND #c #l) #H):-
              (search_k_b #K #c #H),
              (search_k_b #K #l (and  #c #H)).

          "search_o_enc_and" c, l (Apply(AND.clone())):
            (search_o_b #K #K2 #R #M (AND #c #l) #H):-
              (search_o_b #K #K2 #R #M #c #H),
              (search_o_b #K #K2 #R #M #l (and #c #H)).

          // trigger
          "search_o_ind_cca_trigger" :
            (search_o_pre_trigger #K #K #R #T #P #H) :-
              (search_o_trigger #K #R #T #P #H).

          "search_o_enc_kp_trigger" :
            (search_o_pre_trigger #K (IS_FRESH_NONCE #K2) #R #T #P #H) :-
              (search_o_trigger #K #R #T #P #H).

          "search_k_enc_trigger_skip":
            (search_k_trigger (IS_FRESH_NONCE #K) #T #P #H).

          // fa
          "search_o_enc_fa_b_to_k" (FaKeep(CONS_FA_BITSTRING.clone())):
            (search_o_m #K #K2 #R #M (CONS_FA_BITSTRING #A #B) #H):-
              (search_o_m #K #K2 #R #M #B #H),
              (search_k_m #K #A #H),
              (search_k_m #K2 #A #H),
              (FRESH_NONCE #R #A #H).

          "search_o_enc_fa_b_to_k" (FaKeep(CONS_FA_BOOL.clone())):
            (search_o_m #K #K2 #R #M (CONS_FA_BOOL #A #B) #H):-
              (search_o_b #K #K2 #R #M #B #H),
              (search_k_b #K #A #H),
              (search_k_b #K2 #A #H),
              (FRESH_NONCE #R #A #H).

          "search_o_enc_fa_m_fallback" (Apply(CONS_FA_BITSTRING.clone())):
            (search_o_m #K #K2 #R #M (CONS_FA_BITSTRING #A #B) #H):-
              (search_o_m #K #K2 #R #M #A #H),
              (search_o_m #K #K2 #R #M #B #H).

          "search_o_enc_fa_b_to_k" (Apply(CONS_FA_BOOL.clone())):
            (search_o_m #K #K2 #R #M (CONS_FA_BOOL #A #B) #H):-
              (search_o_b #K #K2 #R #M #A #H),
              (search_o_m #K #K2 #R #M #B #H).
        }
    ]
}

fn mk_rule_one(prf @ AEnc { enc, pk, dec, .. }: &AEnc, fun: &Function) -> [PrologRule<Lang>; 2] {
    debug_assert_ne!(fun, dec);
    debug_assert_ne!(fun, pk);
    debug_assert_ne!(fun, &NONCE);
    let inputs = &fun.signature.inputs;

    let args = inputs
        .iter()
        .map(|&x| RecFOFormula::Var(fresh!(x)))
        .collect_vec();

    let (deps_k, deps_o): (Vec<_>, Vec<_>) = izip!(inputs.iter(), &args)
        .filter_map(|(&sort, arg)| {
            let search_k = prf.get_search_k(sort)?;
            let search_o = prf.get_search_o(sort)?;
            Some((
                rexp!((search_k #K #arg #H)),
                rexp!((search_o #K #K2 #R #M #arg #H)),
            ))
        })
        .map(|(x, y)| (Pattern::from(&x), Pattern::from(&y)))
        .unzip();

    let search_k = prf.get_search_k(fun.signature.output).unwrap();
    let search_o = prf.get_search_o(fun.signature.output).unwrap();
    let input_k = Pattern::from(&rexp!((search_k #K (fun #(args.clone())*) #H)));
    let input_o = Pattern::from(&rexp!((search_o #K #K2 #R #M (fun #args*) #H)));

    [
        PrologRule::builder()
            .input(input_k)
            .deps(deps_k)
            .name(format!("search_{enc}_k_{fun}"))
            .payload(ProofHints::Apply(fun.clone()))
            .build()
            .unwrap(),
        PrologRule::builder()
            .input(input_o)
            .deps(deps_o)
            .name(format!("search_{enc}_o_{fun}"))
            .payload(ProofHints::Apply(fun.clone()))
            .build()
            .unwrap(),
    ]
}
