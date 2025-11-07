use std::{borrow::Cow, ops::ControlFlow};

use clap::builder;
use egg::{Id, Pattern, SearchMatches, Searcher};
use golgge::{Dependancy, PrologRule, Rule};
use itertools::{Itertools, chain, izip};
use utils::{ereturn_if, ereturn_let};

use crate::{
    Lang, Problem, fresh,
    problem::{PAnalysis, PRule, RcRule},
    rexp,
    rules::{
        AEnc,
        encryption::{ProofHints, vars::*},
        utils::{SyntaxSearcher, get_protocol},
    },
    runners::SmtRunner,
    terms::{
        AND, BITE, CONS_FA_BITSTRING, CONS_FA_BOOL, Function, IS_FRESH_NONCE, MACRO_EXEC,
        MACRO_FRAME, MACRO_INPUT, MITE, NONCE, PRED, RecFOFormula, Sort, VAMPIRE,
    },
};

pub fn mk_rules<'a>(
    pbl: &'a Problem,
    aenc @ AEnc {
        index,
        search_o_trigger,
        search_k_trigger,
        ..
    }: &'a AEnc,
) -> impl Iterator<Item = RcRule> + use<'a> {
    let trigger_o = Pattern::from(&rexp!((search_o_trigger #K #R #T #P #H)));
    let trigger_k = Pattern::from(&rexp!((search_k_trigger #K #T #P #H)));

    chain![
        mk_static_rules(pbl, aenc).map(|r| r.into_mrc()),
        [(SearchRule {
            aenc: *index,
            trigger_k,
            trigger_o,
            exec: SmtRunner::new(pbl)
        })
        .into_mrc()]
    ]
}

fn mk_static_rules<'a>(
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
        functions.flat_map(|f| mk_rule_one(aenc, &f)),
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
            (search_k_trigger #K #T #P #H).

            "search_o_enc_frame" (Keep):
            (search_k_b #K #K2 #R (MACRO_FRAME #T  #P) #H) :-
            (search_o_pre_trigger #K #K2 #R #T #P #H).

            "search_k_enc_input" (Keep):
            (search_k_m #K (MACRO_INPUT #T  #P) #H) :-
            (search_k_trigger #K (PRED #T) #P #H).

            "search_o_enc_input" (Keep):
            (search_k_b #K #K2 #R (MACRO_INPUT #T  #P) #H) :-
            (search_o_pre_trigger #K #K2 #R (PRED #T) #P #H).

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

            "search_enc_ite_b" c, l, r (Apply(BITE.clone())):
            (search_k_b #K (BITE #c #l #r) #H):-
                (search_k_b #K #c #H),
                (search_k_b #K #l (and #c #H)),
                (search_k_b #K #r (and (not #c) #H)).

            "search_o_enc_ite_m" c, l, r (Apply(BITE.clone())):
            (search_o_b #K #K2 #R (BITE #c #l #r) #H):-
                (search_o_b #K #K2 #R #c #H),
                (search_o_b #K #K2 #R #l (and #c #H)),
                (search_o_b #K #K2 #R #r (and (not #c) #H)).

            "search_enc_and" c, l, r (Apply(AND.clone())):
            (search_k_b #K (AND #c #l) #H):-
                (search_k_b #K #c #H),
                (search_k_b #K #r (and  #c #H)).

            "search_o_enc_and" c, l (Apply(AND.clone())):
            (search_o_b #K #K2 #R (AND #c #l) #H):-
                (search_o_b #K #K2 #R #c #H),
                (search_o_b #K #K2 #R #l (and #c #H)).

            // trigger
            "search_o_ind_cca_trigger" :
              (search_o_pre_trigger #K #K #R #T #P #H) :-
                (search_o_trigger #K #R #T #P #H).

            "search_o_enc_kp_trigger" :
              (search_o_pre_trigger #K (IS_FRESH_NONCE #K2) #R #T #P #H) :-
                (search_o_trigger #K #R #T #P #H).

            "search_k_enc_trigger_skip":
              (search_k_trigger (IS_FRESH_NONCE #K) #T #P #H).
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
                rexp!((search_o #K #K2 #R #arg #H)),
            ))
        })
        .map(|(x, y)| (Pattern::from(&x), Pattern::from(&y)))
        .unzip();

    let search_k = prf.get_search_k(fun.signature.output).unwrap();
    let search_o = prf.get_search_o(fun.signature.output).unwrap();
    let input_k = Pattern::from(&rexp!((search_k #K (fun #(args.clone())*) #H)));
    let input_o = Pattern::from(&rexp!((search_o #K #K2 #R (fun #args*) #H)));

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

#[derive(Debug, Clone)]
struct SearchRule {
    pub aenc: usize,
    pub trigger_k: Pattern<Lang>,
    pub trigger_o: Pattern<Lang>,
    pub exec: SmtRunner,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for SearchRule {
    fn name(&self) -> Cow<'_, str> {
        format!("enc vampire #{:}", self.aenc).into()
    }

    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        let Self {
            aenc,
            trigger_k,
            trigger_o,
            exec,
        } = self;
        let AEnc { pk, dec, .. } = prgm.egraph().analysis.pbl().cryptography()[*aenc]
            .as_aenc()
            .unwrap();
        let pk = pk.clone();
        let dec = dec.clone();

        if let Some(matches) = trigger_k.search_eclass(prgm.egraph(), goal) {
            for subst in matches.substs {
                let [k, t, h] = [K, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| RecFOFormula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = SearchK {
                    aenc: *aenc,
                    pk: pk.clone(),
                    k,
                }
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }

        if let Some(matches) = trigger_o.search_eclass(prgm.egraph(), goal) {
            for subst in matches.substs {
                let [k, k2, r, t, h] = [K, K2, R, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| RecFOFormula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = (SearchO {
                    aenc: *aenc,
                    pk: pk.clone(),
                    dec: dec.clone(),
                    k,
                    k2,
                    r,
                })
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }
        Dependancy::impossible()
    }
}

#[derive(Debug, Clone)]
struct SearchK {
    pub aenc: usize,
    pub pk: Function,
    pub k: RecFOFormula,
}

impl crate::rules::utils::SyntaxSearcher for SearchK {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search k enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        fun == &NONCE || fun == &self.pk
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &crate::rules::utils::fresh::RefFormulaBuilder,
        fun: &Function,
        args: &[RecFOFormula],
    ) -> ControlFlow<()> {
        let Self { pk, k, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k)));
        } else if fun == pk {
            tr!("found {pk}!");

            let ok = args.next().unwrap();
            let builder = builder
                .add_node()
                .condition(rexp!((distinct (NONCE #k) #ok)))
                .build();

            self.inner_search_formula(pbl, &builder, ok.clone());
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}

#[derive(Debug, Clone)]
struct SearchO {
    pub aenc: usize,

    pub pk: Function,
    pub dec: Function,

    pub k: RecFOFormula,
    pub k2: RecFOFormula,
    pub r: RecFOFormula,
}

impl crate::rules::utils::SyntaxSearcher for SearchO {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search o enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, &self.pk, &self.dec].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &crate::rules::utils::fresh::RefFormulaBuilder,
        fun: &Function,
        args: &[RecFOFormula],
    ) -> ControlFlow<()> {
        let Self {
            pk, dec, k2, r, k, ..
        } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k #k2 #r)));
        } else if fun == pk {
            tr!("found {pk}!");

            let arg = args.next().unwrap();
            let builder = builder
                .add_node()
                .condition(rexp!((distinct (NONCE #k) (NONCE #k2) #arg)))
                .build();

            self.inner_search_formula(pbl, &builder, arg.clone());
        } else if fun == dec {
            tr!("found {dec}!");
            let (dm, dk) = args.collect_tuple().unwrap();

            self.inner_search_formula(pbl, builder, dm.clone());
            let builder = builder
                .add_node()
                .condition(rexp!((distinct #dk (NONCE #k) (NONCE #k2))))
                .build();
            self.inner_search_formula(pbl, &builder, dk.clone());
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}
