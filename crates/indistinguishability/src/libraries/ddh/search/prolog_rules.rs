use egg::Pattern;
use golgge::PrologRule;
use itertools::{Itertools, chain, izip};

use crate::libraries::ddh::vars::*;
use crate::libraries::ddh::{DDH, ProofHints};
use crate::terms::{
    AND, BITE, FRESH_NONCE, Formula, Function, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MITE, NONCE,
    PRED, Sort, VAMPIRE,
};
use crate::{Lang, Problem, fresh, rexp};

pub fn mk_static_rules<'a>(
    pbl: &'a Problem,
    aenc @ DDH {
        g,
        exp,
        search_b,
        search_m,
        search_trigger,
        ..
    }: &'a DDH,
) -> impl Iterator<Item = PrologRule<Lang>> + use<'a> {
    let function_to_skip = [
        NONCE.clone(),
        AND.clone(),
        exp.clone(),
        MITE.clone(),
        BITE.clone(),
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
              format!("ddh_{exp}_search_key_a"); (Keep):
              (search_m #NA #NB #NC (NONCE #NA) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              format!("ddh_{exp}_search_key_b"); (Keep):
              (search_m #NA #NB #NC (NONCE #NB) #H) :-!, (VAMPIRE (not #H))
            },
            mk_prolog! {
              format!("ddh_{exp}_search_key_c"); (Keep):
              (search_m #NA #NB #NC (NONCE #NC) #H) :-!, (VAMPIRE (not #H))
            },
        ],
        mk_many_prolog! {
          "search_ddh_false" (Keep):
            (search_m #NA #NB #NC #T false).

          "search_ddh_false" (Keep):
            (search_b #NA #NB #NC #T false).

          "search_ddh_nonce" (Keep):
            (search_m #NA #NB #NC (NONCE #N) #H) :-
              (VAMPIRE (=> #H
                (and (distinct #N #NA) (distinct #N #NB) (distinct #N #NC)))).

          "search_instance" (Replace):
            (search_m #NA #NB #NC (exp (exp g (NONCE #NA)) (NONCE #NB)) #H).

          "search_ddh_exp_ga" (Keep):
            (search_m #NA #NB #NC (exp g (NONCE #NA)) #H).

          "search_ddh_exp_gb" (Keep):
            (search_m #NA #NB #NC (exp g (NONCE #NB)) #H).

          // no need for the case x != g^a^b because then x depens on a and b
          // and would be picked up by `search_ddh_nonce` and such
        },
        functions.map(|f| mk_rule_one(aenc, &f)),
        mk_many_prolog! {
          "search_ddh_exp"(Apply(exp.clone())):
            (search_m #NA #NB #NC (exp #A #B) #H) :-
              (search_m #NA #NB #NC #A #H),
              (search_m #NA #NB #NC #B #H).

          // macros
          "search_ddh_exec"  (Keep):
            (search_b #NA #NB #NC (MACRO_EXEC #T #P) #H) :-
              (search_trigger #NA #NB #T #P #H),
              (FRESH_NONCE #NC (MACRO_FRAME #T  #P) #H).

          "search_ddh_frame"  (Keep):
            (search_m #NA #NB #NC (MACRO_FRAME #T #P) #H) :-
              (search_trigger #NA #NB #T #P #H),
              (FRESH_NONCE #NC (MACRO_FRAME #T  #P) #H).

          "search_ddh_input" (Keep):
            (search_m #NA #NB #NC (MACRO_INPUT #T #P) #H) :-
              (search_trigger #NA #NB (PRED #T) #P #H),
              (FRESH_NONCE #NC (MACRO_FRAME (PRED #T)  #P) #H).

          // if and and
          "search_ddh_ite_m" c, l, r (Apply(MITE.clone())):
            (search_m #NA #NB #NC (MITE #c #l #r) #H):-
              (search_b #NA #NB #NC #c #H),
              (search_m #NA #NB #NC #l (and #c #H)),
              (search_m #NA #NB #NC #r (and (not #c) #H)).

          "search_ddh_ite_b" c, l, r (Apply(BITE.clone())):
            (search_b #NA #NB #NC (BITE #c #l #r) #H):-
              (search_b #NA #NB #NC #c #H),
              (search_b #NA #NB #NC #l (and #c #H)),
              (search_b #NA #NB #NC #r (and (not #c) #H)).

          "search_ddh_and" c, l (Apply(AND.clone())):
            (search_b #NA #NB #NC (AND #c #l) #H):-
              (search_b #NA #NB #NC #c #H),
              (search_b #NA #NB #NC #l (and  #c #H)).
        }
    ]
}

fn mk_rule_one(ddh @ DDH { exp, .. }: &DDH, fun: &Function) -> PrologRule<Lang> {
    debug_assert_ne!(fun, exp);
    debug_assert_ne!(fun, &NONCE);
    let inputs = &fun.signature.inputs;

    let args = inputs
        .iter()
        .map(|&x| Formula::Var(fresh!(x)))
        .collect_vec();

    let deps = izip!(inputs.iter(), &args)
        .filter_map(|(&sort, arg)| {
            let search = ddh.get_search(sort)?;
            Some(rexp!((search #NA #NB #NC #arg #H)))
        })
        .map(|x| Pattern::from(&x));

    let search = ddh.get_search(fun.signature.output).unwrap();
    let input = Pattern::from(&rexp!((search #NA #NB #NC (fun #(args.clone())*) #H)));

    PrologRule::builder()
        .input(input)
        .deps(deps)
        .name(format!("search_ddh_{exp}_{fun}"))
        .payload(ProofHints::Apply(fun.clone()))
        .build()
        .unwrap()
}
