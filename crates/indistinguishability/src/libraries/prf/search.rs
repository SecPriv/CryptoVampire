use std::borrow::Cow;
use std::ops::ControlFlow;

use egg::{Pattern, Searcher};
use golgge::{Dependancy, PrologRule, Rule};
use itertools::{Itertools, chain, izip};
use utils::{ereturn_if, ereturn_let};

use super::PRFProof::*;
use crate::libraries::PRF;
use crate::libraries::utils::fresh::RefFormulaBuilder;
use crate::libraries::utils::{SyntaxSearcher, get_protocol};
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::protocol::{Protocol, Step};
use crate::runners::SmtRunner;
use crate::terms::{
    AND, BITE, Formula, Function, HAPPENS, IS_FRESH_NONCE, LT, MACRO_COND, MACRO_EXEC, MACRO_FRAME,
    MACRO_INPUT, MACRO_MSG, MITE, NONCE, PRED, Sort, UNFOLD_COND, UNFOLD_MSG, VAMPIRE,
};
use crate::{CVProgram, Lang, Problem, fresh, rexp};

decl_vars!(const M:Bitstring, K:Nonce, P:Protocol, T:Time, H:Bool, N_PRF:Nonce);

// =========================================================
// ==================== prolog search ======================
// =========================================================

/// Creates an iterator of all prolog and search rules related to PRF analysis.
///
/// These rules are used to guide the e-graph search for PRF indistinguishability.
pub fn mk_rules<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = RcRule> + use<'a> {
    // let functions = pbl
    //     .functions()
    //     .iter_current()
    //     .filter(|f| f != &&NONCE && f != &&prf.hash)
    //     .filter(|f| !f.is_out_of_term_algebra())
    //     .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
    //     .filter(|f| !f.is_special_subterm() || f.is_if_then_else())
    //     .cloned();

    let prolog_rules = mk_static_rules(pbl, prf);

    let search_rules = [PrfVampireRule::new(pbl, prf)];

    chain![
        prolog_rules.map(|p| p.into_mrc()),
        search_rules.map(|p| p.into_mrc())
    ]
}

/// basic search rule
///
/// ```text
///  m,k ||> x1 ... m,k ||> xn
/// ---------------------------
///    m,k ||> f(x1,...,xn)
/// ```
fn mk_rule_one(prf: &PRF, fun: Function) -> PrologRule<Lang> {
    debug_assert_ne!(fun, prf.hash);
    debug_assert_ne!(fun, NONCE);
    let inputs = &fun.signature.inputs;

    let args = inputs
        .iter()
        .map(|&x| Formula::Var(fresh!(x)))
        .collect_vec();

    let deps = izip!(inputs.iter(), &args)
        .filter_map(|(&sort, arg)| {
            let search = prf.get_search(sort)?;
            Some(rexp!((search #M #K #N_PRF #arg #H)))
        })
        .map(|x| Pattern::from(&x))
        .collect_vec();

    let search = prf.get_search(fun.signature.output).unwrap();
    let input = Pattern::from(&rexp!((search #M #K #N_PRF (fun #args*) #H)));

    PrologRule::builder()
        .input(input)
        .deps(deps)
        .name(format!("search_prf_{fun}"))
        .payload(Apply(fun))
        .build()
        .unwrap()
}

fn mk_static_rules(
    pbl: &Problem,
    prf @ PRF {
        search_bitstring: search_m,
        search_bool: search_b,
        search_trigger,
        hash,
        ..
    }: &PRF,
) -> impl Iterator<Item = PrologRule<Lang>> {
    let functions = pbl
        .functions()
        .iter_current()
        .filter(|f| f != &&NONCE && f != &&prf.hash)
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm())
        .filter(|f| *f != &AND)
        .cloned();
    decl_vars!(m, k, m2, k2, h, n, nprf);
    chain![
        [
            // search axiom
            //
            // ```text
            // ---------------------
            //  not(m, k, nprf ||> k | _)
            // ```
            //
            // We represent it in prolog using `fail` and `!`, so it is
            //
            // ```text
            // m, k, nprf ||> k | _ :- !, fail
            // ```
            //
            // ### soundness
            // This *needs* to be in front of the [mk_rule_one] for [NONCE].
            mk_prolog! {
                "search_prf_found_key"; m, k, h (Keep):
                (search_m #m #k #nprf (NONCE #k) #h) :-!,
                    (VAMPIRE (not #h))
            }
        ],
        mk_many_prolog! {
            "search_prf_false" (Keep):
            (search_m #m #k #nprf #m2 false).

            // ```text
            //  |- h => k != n
            // -----------
            //  m,k ||> n | h
            // ```
            "search_prf_nonce" (Keep):
            (search_m #m #k #nprf (NONCE #n) #h) :-
                (VAMPIRE (=> #h (distinct #k #n))),
                (VAMPIRE (=> #h (distinct #nprf #n)))
                .

            // ```text
            // ---------------------
            //  m, k ||> hash(m, (nonce k))
            // ```
            //
            // this means that it will be captured by the substitution
            "search_prf_found_instance" (Instance):
            (search_m #m #k #nprf (hash #m (NONCE #k)) #h).
        },
        functions.map(|f| mk_rule_one(prf, f)),
        mk_many_prolog! {
            // If [egg] can't prove that `m = m'` (e.g., we didn't trigger
            // [mk_search_rule_found_instance]). Then we need to prove that `m` and
            // `m'` trully are different otherwise the axiom will fail
            //
            // ```text
            //  |- m != m'   m, k ||> m'
            // -------------------------
            //    m, k ||> hash(m', k)
            // ```
            "search_prf_neq_m" (Apply(hash.clone())):
            (search_m #m #k #nprf (hash #m2 (NONCE #k)) #h) :-
                (VAMPIRE (=> #h (distinct #m #m2))),
                (search_m #m #k #nprf #m2 #h).



            // If [egg] can't prove that `k = k'`. Then we need to prove that `k` and
            // `k'` trully are different otherwise the axiom will fail
            //
            // ```text
            //  |- k != k'   m, k ||> m'   m, k ||> k'
            // ---------------------------------------
            //         m, k ||> hash(m', k')
            // ```
            "search_prf_neq_k" (Apply(hash.clone())):
            (search_m #m #k #nprf (hash #m2  #k2) #h) :-
                (VAMPIRE (=> #h (distinct (NONCE #k) #k2))),
                (VAMPIRE (=> #h (distinct (NONCE #nprf) #k2))),
                (search_m #m #k #nprf #m2 #h),
                (search_m #m #k #nprf #k2 #h).


            // macros
            "search_prf_exec" p, t (Keep):
            (search_b #m #k (IS_FRESH_NONCE #nprf) (MACRO_EXEC #t  #p) #h) :-
            (search_trigger #m #k #p #t #h).

            "search_prf_frame" p, t (Keep):
            (search_m #m #k (IS_FRESH_NONCE #nprf) (MACRO_FRAME #t  #p) #h) :-
            (search_trigger #m #k #p #t #h).

            "search_prf_input" p, t (Keep):
            (search_m #m #k (IS_FRESH_NONCE #nprf) (MACRO_INPUT #t  #p) #h) :-
            (search_trigger #m #k #p (PRED #t) #h).

            // if and and
            "search_prf_ite_m" c, l, r (Apply(MITE.clone())):
            (search_m #m #k #nprf (MITE #c #l #r) #h):-
                (search_b #m #k #nprf #c #h),
                (search_m #m #k #nprf #l (and #c #h)),
                (search_m #m #k #nprf #r (and (not #c) #h)).

            "search_prf_ite_b" c, l, r (Apply(BITE.clone())):
            (search_b #m #k #nprf (BITE #c #l #r) #h):-
                (search_b #m #k #nprf #c #h),
                (search_b #m #k #nprf #l (and #c #h)),
                (search_b #m #k #nprf #r (and (not #c) #h)).

            "search_prf_and" a, b (Apply(AND.clone())):
            (search_b #m #k #nprf (AND #a #b) #h):-
                (search_b #m #k #nprf #a #h),
                (search_b #m #k #nprf #b (and #a #h)).

            // ~~~~~~~~~~~~~~~~ macros ~~~~~~~~~~~~~~~~~~

            "serach_prf_msg" t, p (Apply(MACRO_MSG.clone())):
            (search_m #m #k #nprf (MACRO_MSG #t #p) #h):-
                (VAMPIRE (=> #h (HAPPENS #t))),
                (search_m #m #k #nprf (UNFOLD_MSG #t #p) #h).

            "serach_prf_cond" t, p (Apply(MACRO_COND.clone())):
            (search_b #m #k #nprf (MACRO_COND #t #p) #h):-
                (VAMPIRE (=> #h (HAPPENS #t))),
                (search_b #m #k #nprf (UNFOLD_COND #t #p) #h).

        }
    ]
}

// =========================================================
// ====================== CV Search ========================
// =========================================================

/// Represents a search context for PRF analysis.
#[derive(Debug)]
pub struct Search {
    /// The index of the PRF being searched.
    pub prf_idx: usize,
    /// The message `m` in the PRF context.
    pub m: Formula,
    /// The key `k` in the PRF context.
    pub k: Formula,
}

impl Search {
    /// Returns a reference to the PRF associated with this search context.
    #[inline]
    fn prf<'a>(&self, pbl: &'a Problem) -> &'a PRF {
        pbl.cryptography()[self.prf_idx].as_inner().unwrap()
    }

    /// Returns an iterator of formula instead of a large conjunctrion
    /// Searches for PRF-related conditions at a specific timepoint within a protocol.
    pub fn search_timepoint<'a>(
        &'a self,
        pbl: &'a Problem,
        ptcl: &'a Protocol,
        time: Formula,
        hyp: Formula,
    ) -> impl Iterator<Item = Formula> + use<'a> {
        tr!("searching protocol {}", ptcl.name());
        ptcl.steps()
            .iter()
            .flat_map(
                move |step @ Step {
                          id,
                          vars,
                          cond,
                          msg,
                          ..
                      }| {
                    let vars = vars.iter().map(|v| Formula::Var(v.clone()));
                    let s = rexp!((id #vars*));

                    let condition = rexp!((and #hyp (HAPPENS #s) (LT #s #time)));
                    [
                        (condition.clone(), cond, step),
                        (condition.clone(), msg, step),
                    ]
                    .into_iter()
                },
            )
            .map(|(condition, to_search, Step { vars, .. })| {
                let builder = RefFormulaBuilder::builder()
                    .condition(condition)
                    .variables(vars.clone())
                    .forall()
                    .build();
                self.inner_search_formula(pbl, &builder, to_search.clone());
                builder.into_inner().unwrap().into_formula()
            })
            .flat_map(|x| x.split_conjunction())
    }
}

impl crate::libraries::utils::SyntaxSearcher for Search {
    /// Returns a debug name for the PRF searcher.
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search_prf")
    }

    /// Checks if the given function is an instance relevant to this PRF search (i.e., `NONCE` or the PRF's hash function).
    fn is_instance(&self, pbl: &Problem, fun: &Function) -> bool {
        fun == &NONCE || fun == &self.prf(pbl).hash
    }

    /// Processes an instance of a relevant function, updating the formula builder based on PRF logic.
    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { m, k, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k)));
        } else if fun == &self.prf(pbl).hash {
            tr!("found hash!");
            let (m2, k2) = args
                .collect_tuple()
                .expect("wrong parameters given to a hash");
            builder.add_leaf(rexp!((or (distinct #k2 (NONCE #k)) (distinct #m2 #m))));
            self.inner_search_formula(pbl, builder, m2.clone());
            {
                let builder = builder
                    .add_node()
                    .condition(rexp!((distinct #k2 (NONCE #k))))
                    .forall()
                    .build();

                self.inner_search_formula(pbl, &builder, k2.clone());
            }
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}

// =========================================================
// ======================== Rule ===========================
// =========================================================

/// A rule that triggers the PRF analysis using the Vampire SMT solver.
#[derive(Debug)]
struct PrfVampireRule {
    /// The index of the PRF in the problem's cryptographic assumptions.
    prf: usize,
    /// The pattern to search for in the e-graph that triggers this rule.
    pattern: Pattern<Lang>,
    /// The SMT runner used to interact with the Vampire SMT solver.
    exec: SmtRunner,
}

impl PrfVampireRule {
    /// Creates a new `PrfVampireRule`.
    fn new(pbl: &Problem, prf @ PRF { search_trigger, .. }: &PRF) -> Self {
        Self {
            prf: prf.index(),
            pattern: Pattern::from(&rexp!((search_trigger #M #K #P #T #H))),
            exec: SmtRunner::new(pbl),
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for PrfVampireRule {
    /// Returns the name of this rule, including the PRF index.
    fn name(&self) -> std::borrow::Cow<'_, str> {
        format!("prf vampire #{:}", self.prf).into()
    }

    /// Searches for the trigger pattern in the e-graph and initiates a PRF search using the SMT solver.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: egg::Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) = self.pattern
                .search_eclass(egraph, goal), Dependancy::impossible());

        for subst in substs.substs {
            let mut cache = Default::default();
            let [m, k, time, hyp] = [M, K, T, H].map(|x| {
                Formula::try_from_id_cached(egraph, *subst.get(x.as_egg()).unwrap(), &mut cache)
                    .unwrap()
            });
            let pbl = egraph.analysis.pbl();
            let search = Search {
                prf_idx: self.prf,
                m,
                k,
            };
            // get the protocol from the function
            let ptcl = get_protocol(egraph, *subst.get(P.as_egg()).unwrap()).unwrap();

            let search = search.search_timepoint(pbl, ptcl, time, hyp).collect_vec();
            tr!(
                "prf needs to checks:\n[\n\t{}\n]",
                search.iter().join("\n\t")
            );
            let pbl = egraph.analysis.pbl_mut();
            pbl.find_temp_quantifiers(&search);
            let result = search.into_iter().all(|query| {
                let query = query.as_smt(*pbl).unwrap();
                self.exec.run_to_dependancy(pbl, query).is_axioms()
            });
            pbl.clear_temp_quantifiers();
            ereturn_if!(result, Dependancy::axiom());
        }

        Dependancy::impossible()
    }
}
