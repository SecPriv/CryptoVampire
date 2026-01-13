use egg::Pattern;
use golgge::PrologRule;
use itertools::{Itertools, chain, izip};

use crate::libraries::AEnc;
use crate::libraries::aenc::ProofHints;
use crate::libraries::aenc::vars::*;
use crate::libraries::utils::TwoSortFunction;
use crate::terms::{
    AND, BITE, CONS_FA_BITSTRING, CONS_FA_BOOL, FRESH_NONCE, Formula, Function, HAPPENS,
    IS_FRESH_NONCE, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MSG, MITE, NONCE, PRED,
    Sort, UNFOLD_COND, UNFOLD_MSG, VAMPIRE,
};
use crate::{Lang, Problem, fresh, rexp};

fn function_to_skip(aenc: &AEnc, f: &Function) -> bool {
    [&NONCE, &aenc.dec, &AND, &CONS_FA_BITSTRING, &CONS_FA_BOOL].contains(&f)
        || if let Some(pk) = &aenc.pk {
            f == pk
        } else {
            f == &aenc.enc
        }
}

/// Build the static rule for search for the ENC-KP and IND-CCA1 axioms
///
/// ## Implementation notes
/// - crypto function may require special care while rebuilding terms. This
///   applies to:
///   * `pk`
///   * `dec`
/// - `search_o` isn't for rebuilds of terms. Hence it doesn't have proofs
///   attached
/// - We split the static search of `search_k` like we did for `search_o`. See
///   [AEnc::search_k_trigger].
pub fn mk_static_rules<'a>(
    pbl: &'a Problem,
    aenc @ AEnc {
        enc,
        dec,
        pk,
        search_k: TwoSortFunction {
            m: search_k_m,
            b: search_k_b,
        },
        search_o: TwoSortFunction {
            m: search_o_m,
            b: search_o_b,
        },
        search_k_trigger,
        search_k_pre_trigger,
        search_o_trigger,
        ..
    }: &'a AEnc,
) -> impl Iterator<Item = PrologRule<Lang>> + use<'a> {
    let functions = pbl
        .functions()
        .iter_current()
        .filter(|f| !function_to_skip(aenc, f))
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm())
        .cloned();
    use super::super::ProofHints::*;

    let mpk = if let Some(pk) = pk {
        rexp!((pk (NONCE #K)))
    } else {
        rexp!((NONCE #K))
    };

    chain![
        [
            // Reject when we find a key, these are shortcuts
            mk_prolog! {
              "search_k_enc_key"; (Keep):
              (search_k_m #K #K2 #R #M (NONCE #K) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_k_enc_key2"; (Keep):
              (search_k_m #K #K2 #R #M (NONCE #K2) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_k_enc_rand"; (Keep):
              (search_k_m #K #K2 #R #M (NONCE #R) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              "search_o_enc_key"; :
              (search_o_m #K (NONCE #K) #H) :-!, (VAMPIRE (not #H))
            },
        ],
        mk_many_prolog! {
          // ~~~~~~~~~~~ trivially false ~~~~~~~~~~~~~~
          "search_k_m_enc_false" (Keep):
            (search_k_m #K #K2 #R #M #T false).
          "search_k_m_enc_false" (Keep):
            (search_k_b #K #K2 #R #M #T false).

          "search_o_m_enc_false" :
            (search_o_m #K #T false).
          "search_o_b_enc_false" :
            (search_o_b #K #T false).

          // ~~~~~~~~~~~ nonce encounters ~~~~~~~~~~~~~
          "search_k_enc_nonce" (Keep):
            (search_k_m #K #K2 #R #M (NONCE #N) #H) :-
              (VAMPIRE (=> #H (distinct #K #N))),
              (VAMPIRE (=> #H (distinct #K2 #N))),
              (VAMPIRE (=> #H (distinct #R #N))).

          "search_o_enc_nonce" :
            (search_o_m #K (NONCE #N) #H) :-
              (VAMPIRE (=> #H (distinct #K #N))).

          // ~~~~~~~~~~~~~~~ instance ~~~~~~~~~~~~~~~~~
          "search_k_instance" (Replace):
            (search_k_m #K #K2 #R #M (enc #M (NONCE #R) #mpk) #H).
        },
        // =========================================================
        // =================== general search ======================
        // =========================================================
        functions.flat_map(|f| mk_rule_one(aenc, &f)),
        // ~~~~~~~~~~~~ rules with pk ~~~~~~~~~~~~~~~
        if let Some(pk) = pk {
            mk_many_prolog! {
              // ~~~~~~~~~~~~~~~~~~ pk ~~~~~~~~~~~~~~~~~~~~
              "search_k_enc_pk_k" (Keep):
                (search_k_m #K #K2 #R #M (pk (NONCE #K)) #H).
              "search_k_enc_pk_k2" (Keep):
                (search_k_m #K #K2 #R #M (pk (NONCE #K2)) #H).

              "search_k_enc_pk_neq" (Apply(pk.clone())):
                (search_k_m #K #K2 #R #M (pk #T) #H) :-
                  (search_k_m #K #K2 #R #M #T #H),
                  (VAMPIRE (=> #H (distinct #T (NONCE #K)))),
                  (VAMPIRE (=> #H (distinct #T (NONCE #R)))),
                  (VAMPIRE (=> #H (distinct #T (NONCE #K2)))).

              "search_o_enc_pk_k" :
                (search_o_m #K (pk (NONCE #K)) #H).

              "search_o_enc_pk_neq" :
                (search_o_m #K (pk #T) #H) :-
                  (search_o_m #K #T #H),
                  (VAMPIRE (=> #H (distinct #T (NONCE #K)))).

              // ~~~~~~~~~~~~~~~~~ dec ~~~~~~~~~~~~~~~~~~~~
              // This behaves a lot like `pk` so we offload to the pk rules.
              // This needs to be taken into account while rebuilding the term
              "search_k_enc_dec" (Apply(dec.clone())):
                (search_k_m #K #K2 #R #M (dec #A #B) #H) :-
                  (search_k_m #K #K2 #R #M #A #H),
                  (search_k_m #K #K2 #R #M (pk #B) #H).

              "search_o_enc_dec" :
                (search_o_m #K (dec #A #B) #H):-
                  (search_o_m #K #A #H),
                  (search_o_m #K (pk #B) #H).
            }
        } else {
            mk_many_prolog! {
              // ~~~~~~~~~~~~~~~~~ dec ~~~~~~~~~~~~~~~~~~~~
              // This behaves a lot like `pk` so we offload to the pk rules.
              // This needs to be taken into account while rebuilding the term
              "search_k_enc_dec" (Apply(dec.clone())):
                (search_k_m #K #K2 #R #M (dec #A (NONCE #K)) #H) :-
                  (search_k_m #K #K2 #R #M #A #H).

              "search_k_enc_dec2" (Apply(dec.clone())):
                (search_k_m #K #K2 #R #M (dec #A (NONCE #K2)) #H) :-
                  (search_k_m #K #K2 #R #M #A #H).

              "search_k_enc_dec_neq" (Apply(dec.clone())):
                (search_k_m #K #K2 #R #M (dec #A #B) #H) :-
                  (search_k_m #K #K2 #R #M #A #H),
                  (search_k_m #K #K2 #R #M #B #H).

              "search_o_enc_dec" :
                (search_o_m #K (dec #A (NONCE #K)) #H):-
                  (search_o_m #K #A #H).

              "search_o_enc_dec_neq" :
                (search_o_m #K (dec #A #B) #H):-
                  (search_o_m #K #A #H),
                  (search_o_m #K #B #H).

              // enc

              "search_k_enc_enc" (Apply(enc.clone())):
                (search_k_m #K #K2 #R #M (enc #T #A #B) #H) :-
                  (search_k_m #K #K2 #R #M #T #H),
                  (search_k_m #K #K2 #R #M #A #H),
                  (search_k_m #K #K2 #R #M #B #H).

              // TODO: make sure this is sound
              "search_o_enc_enc" :
                (search_o_m #K (enc #T (NONCE #A) (NONCE #B)) #H):-
                  (search_o_m #K #T #H).

              "search_o_enc_enc_2" :
                (search_o_m #K (enc #T  #A #B) #H):-
                  (search_o_m #K #T #H),
                  (search_o_m #K #A #H),
                  (search_o_m #K #B #H).
            }
        },
        mk_many_prolog! {
          // ~~~~~~~~~~~~~~~~ macros ~~~~~~~~~~~~~~~~~~
          "search_k_enc_exec"  (Keep):
            (search_k_b #K #K2 #R #M (MACRO_EXEC #T #P) #H) :-
              (search_k_pre_trigger #K #K2 #R #T #P #H).

          "search_o_enc_exec"  :
            (search_o_b #K (MACRO_EXEC #T #P) #H) :-
              (search_o_trigger #K #T #P #H).

          "search_k_enc_frame"  (Keep):
            (search_k_m #K #K2 #R #M (MACRO_FRAME #T #P) #H) :-
              (search_k_pre_trigger #K #K2 #R #T #P #H).

          "search_o_enc_frame" :
            (search_o_m #K (MACRO_FRAME #T  #P) #H) :-
              (search_o_trigger #K #T #P #H).

          "search_k_enc_input" (Keep):
            (search_k_m #K #K2 #R #M (MACRO_INPUT #T  #P) #H) :-
              (search_k_pre_trigger #K #K2 #R (PRED #T) #P #H).

          "search_o_enc_input" :
            (search_o_m #K (MACRO_INPUT #T  #P) #H) :-
              (search_o_trigger #K (PRED #T) #P #H).

          // ~~~~~~~~~~~~~~ if and and ~~~~~~~~~~~~~~~~
          "search_k_enc_ite_m" c, l, r (Apply(MITE.clone())):
            (search_k_m #K #K2 #R #M (MITE #c #l #r) #H):-
              (search_k_b #K #K2 #R #M #c #H),
              (search_k_m #K #K2 #R #M #l (and #c #H)),
              (search_k_m #K #K2 #R #M #r (and (not #c) #H)).

          "search_o_enc_ite_m" c, l, r :
            (search_o_m #K (MITE #c #l #r) #H):-
              (search_o_b #K #c #H),
              (search_o_m #K #l (and #c #H)),
              (search_o_m #K #r (and (not #c) #H)).

          "search_k_enc_ite_b" c, l, r (Apply(BITE.clone())):
            (search_k_b #K #K2 #R #M (BITE #c #l #r) #H):-
              (search_k_b #K #K2 #R #M #c #H),
              (search_k_b #K #K2 #R #M #l (and #c #H)),
              (search_k_b #K #K2 #R #M #r (and (not #c) #H)).

          "search_o_enc_ite_b" c, l, r :
            (search_o_b #K (BITE #c #l #r) #H):-
              (search_o_b #K #c #H),
              (search_o_b #K #l (and #c #H)),
              (search_o_b #K #r (and (not #c) #H)).

          "search_k_enc_and" c, l (Apply(AND.clone())):
            (search_k_b #K #K2 #N #M (AND #c #l) #H):-
              (search_k_b #K #K2 #N #M #c #H),
              (search_k_b #K #K2 #N #M #l (and  #c #H)).

          "search_o_enc_and" c, l :
            (search_o_b #K (AND #c #l) #H):-
              (search_o_b #K #c #H),
              (search_o_b #K #l (and #c #H)).

          // ~~~~~~~~~~~~~~~ trigger ~~~~~~~~~~~~~~~~~~
          "search_k_pre_trigger" :
            (search_k_pre_trigger #K #K2 #R #T #P #H) :-
              (search_k_trigger #K #T #P #H),
              (search_k_trigger #K2 #T #P #H),
              (FRESH_NONCE #R (MACRO_FRAME #T #P) #H).
          "search_k_trigger_skip":
            (search_k_trigger (IS_FRESH_NONCE #K2) #T #P #H).

          "search_o_trigger_skip" :
            (search_o_trigger (IS_FRESH_NONCE #K) #T #P #H).

          // ~~~~~~~~~~~~~~~~~~ fa ~~~~~~~~~~~~~~~~~~~~
          // strong -> means it is tighter and looks on both side
          // weak -> strong fails and fallbacks to using oracles (and no instances then)
          "search_k_enc_fa_m_strong" (Apply(CONS_FA_BITSTRING.clone())):
            (search_k_m #K #K2 #R #M (CONS_FA_BITSTRING #A #B) #H):-
              (search_k_m #K #K2 #R #M #A #H),
              (search_k_m #K #K2 #R #M #B #H).
          "search_k_enc_fa_b_strong" (Apply(CONS_FA_BOOL.clone())):
            (search_k_m #K #K2 #R #M (CONS_FA_BOOL #A #B) #H):-
              (search_k_b #K #K2 #R #M #A #H),
              (search_k_m #K #K2 #R #M #B #H).

          // first `B` then `A`
          "search_k_enc_fa_m_weak" (FaKeep(CONS_FA_BITSTRING.clone())):
            (search_k_m #K #K2 #R #M (CONS_FA_BITSTRING #A #B) #H):-
              (search_k_m #K #K2 #R #M #B #H),

              (search_o_m #K #A #H),
              (search_o_m #K2 #A #H),
              (FRESH_NONCE #R #A #H).

          "search_k_enc_fa_b_weak" (FaKeep(CONS_FA_BOOL.clone())):
            (search_k_m #K #K2 #R #M (CONS_FA_BOOL #A #B) #H):-
              (search_k_m #K #K2 #R #M #B #H),

              (search_o_b #K #A #H),
              (search_o_b #K2 #A #H),
              (FRESH_NONCE #R #A #H).

          // ~~~~~~~~~~~~~~~~ macros ~~~~~~~~~~~~~~~~~~
          "search_o_enc_msg":
            (search_o_m #K (MACRO_MSG #T #P) #H):-
              (VAMPIRE (=> #H (HAPPENS #T))),
              (search_o_m #K (UNFOLD_MSG #T #P) #H).

          "search_o_enc_cond":
            (search_o_b #K (MACRO_COND #T #P) #H):-
              (VAMPIRE (=> #H (HAPPENS #T))),
              (search_o_b #K (UNFOLD_COND #T #P) #H).
        }
    ]
}

fn mk_rule_one(
    _prf @ AEnc {
        enc,
        pk,
        dec,
        search_k,
        search_o,
        ..
    }: &AEnc,
    fun: &Function,
) -> [PrologRule<Lang>; 2] {
    debug_assert_ne!(fun, dec);
    debug_assert_ne!(Some(fun), pk.as_ref());
    debug_assert_ne!(fun, &NONCE);
    let inputs = &fun.signature.inputs;

    let args = inputs
        .iter()
        .map(|&x| Formula::Var(fresh!(x)))
        .collect_vec();

    let (deps_k, deps_o): (Vec<_>, Vec<_>) = izip!(inputs.iter(), &args)
        .filter_map(|(&sort, arg)| {
            let search_k = search_k.form_sort(sort)?;
            let search_o = search_o.form_sort(sort)?;
            Some((
                rexp!((search_k #K #K2 #R #M #arg #H)),
                rexp!((search_o #K #arg #H)),
            ))
        })
        .map(|(x, y)| (Pattern::from(&x), Pattern::from(&y)))
        .unzip();

    let search_k = search_k.form_sort(fun.signature.output).unwrap();
    let search_o = search_o.form_sort(fun.signature.output).unwrap();
    let input_k = Pattern::from(&rexp!((search_k #K #K2 #R #M (fun #(args.clone())*) #H)));
    let input_o = Pattern::from(&rexp!((search_o #K (fun #args*) #H)));

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
