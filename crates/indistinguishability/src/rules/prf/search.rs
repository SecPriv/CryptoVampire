use std::borrow::Cow;
use std::ops::ControlFlow;
use std::rc::Rc;

use egg::{Pattern, Searcher};
use golgge::{Dependancy, PrologRule, Rule};
use itertools::{Itertools, chain, izip};
use utils::{ereturn_if, ereturn_let};

use crate::problem::{PAnalysis, PRule, RcRule};
use crate::protocol::{Protocol, Step};
use crate::rules::PRF;
use crate::rules::utils::SyntaxSearcher;
use crate::rules::utils::fresh::RefFormulaBuilder;
use crate::terms::{
    FAIL, Function, HAPPENS, LT, MACRO_EXEC, MACRO_FRAME, NONCE, RecFOFormula, Sort, VAMPIRE,
};
use crate::vampire::runner::VampireExec;
use crate::{Lang, Problem, fresh, rexp};

declare_trace!($"search_prf");

// =========================================================
// ==================== prolog search ======================
// =========================================================

pub fn mk_rules<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = RcRule> + use<'a> {
    let functions = pbl
        .functions()
        .iter_current()
        .filter(|f| f != &&NONCE && f != &&prf.hash)
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm() || f.is_if_then_else())
        .cloned();

    let prolog_rules = chain![
        [
            mk_rule_found_instance(prf),
            mk_rule_found_key(prf),
            mk_rule_nonce(prf),
        ],
        functions.map(|f| mk_rule_one(prf, f)),
        [
            mk_rule_neq_m(prf),
            mk_rule_neq_k(prf),
            mk_rule_exec(prf),
            mk_rule_frame(prf)
        ],
    ];

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

    decl_vars!(m, k);
    let args = inputs
        .iter()
        .map(|&x| RecFOFormula::Var(fresh!(x)))
        .collect_vec();

    let deps = izip!(inputs.iter(), &args)
        .filter_map(|(&sort, arg)| {
            let search = prf.get_search(sort)?;
            Some(rexp!((search #m #k #arg)))
        })
        .map(|x| Pattern::from(&x))
        .collect_vec();

    let search = prf.get_search(fun.signature.output).unwrap();
    let input = Pattern::from(&rexp!((search #m #k (fun #args*))));

    PrologRule::builder()
        .input(input)
        .deps(deps)
        .name(format!("search_prf_{fun}"))
        .build()
        .unwrap()
}

/// search rule for nonces
///
/// ```text
///  |- k != n
/// -----------
///  m,k ||> n
/// ```
fn mk_rule_nonce(
    PRF {
        search_bitstring: search,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_nonce"; m, k, n:
        (search #m #k (NONCE #n)) :-
            (VAMPIRE (distinct #k #n))
    }
}

/// search axiom
///
/// ```text
/// ---------------------
///  m, k ||> hash(m, k)
/// ```
///
/// this means that it will be captured by the substitution
fn mk_rule_found_instance(
    PRF {
        hash,
        search_bitstring: search,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_found_instance"; m, k:
        (search #m #k (hash #m #k))
    }
}

/// search axiom
///
/// ```text
/// ---------------------
///  not(m, k ||> k)
/// ```
///
/// We represent it in prolog using `fail` and `!`, so it is
///
/// ```text
/// m, k ||> k :- !, fail
/// ```
///
/// ### soundness
/// This *needs* to be in front of the [mk_rule_one] for [NONCE].
fn mk_rule_found_key(
    PRF {
        search_bitstring: search,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_found_key"; m, k:
        (search #m #k (NONCE #k)) :-!, FAIL
    }
}

/// If [egg] can't prove that `m = m'` (e.g., we didn't trigger
/// [mk_search_rule_found_instance]). Then we need to prove that `m` and
/// `m'` trully are different otherwise the axiom will fail
///
/// ```text
///  |- m != m'   m, k ||> m'
/// -------------------------
///    m, k ||> hash(m', k)
/// ```
fn mk_rule_neq_m(
    PRF {
        hash,
        search_bitstring: search,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_neq_m"; m, k, m2:
        (search #m #k (hash #m2 (NONCE #k))) :-
            (VAMPIRE (distinct #m #m2)),
            (search #m #k #m2)
    }
}

/// If [egg] can't prove that `k = k'`. Then we need to prove that `k` and
/// `k'` trully are different otherwise the axiom will fail
///
/// ```text
///  |- k != k'   m, k ||> m'   m, k ||> k'
/// ---------------------------------------
///         m, k ||> hash(m', k')
/// ```
fn mk_rule_neq_k(
    PRF {
        hash,
        search_bitstring: search,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_neq_k"; m, k, m2, k2:
        (search #m #k (hash #m2 (NONCE #k2))) :-
            (VAMPIRE (distinct #k #k2)),
            (search #m #k #m2),
            (search #m #k #k2)
    }
}

/// deep search on `exec`
///
/// ```text
///  search(m, k, p, t)
/// --------------------
///  m, k ||> exec(p)@t
/// ```
/// **NB**: there is no distinction between `exec` and `frame`, they both search
/// everywhere
fn mk_rule_exec(
    PRF {
        search_bool: search,
        search_trigger,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_exec"; m, k, p, t:
        (search #m #k (MACRO_EXEC #t  #p)) :-
        (search_trigger #m #k #p #t)
    }
}

/// deep search on `frame`
///
/// ```text
///  search(m, k, p, t)
/// --------------------
///  m, k ||> frame(p)@t
/// ```
fn mk_rule_frame(
    PRF {
        search_bitstring: search,
        search_trigger,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    mk_prolog! {
        "search_prf_frame"; m, k, p, t:
        (search #m #k (MACRO_FRAME #t  #p)) :-
        (search_trigger #m #k #p #t)
    }
}

// =========================================================
// ====================== CV Search ========================
// =========================================================

#[derive(Debug)]
pub struct Search {
    pub prf_idx: usize,
    pub m: RecFOFormula,
    pub k: RecFOFormula,
}

impl Search {
    #[inline]
    fn prf<'a>(&self, pbl: &'a Problem) -> &'a PRF {
        pbl.cryptography()[self.prf_idx].as_prf().unwrap()
    }

    /// Returns an iterator of formula instead of a large conjunctrion
    pub fn search_timepoint<'a>(
        &'a self,
        pbl: &'a Problem,
        ptcl: &'a Protocol,
        time: RecFOFormula,
    ) -> impl Iterator<Item = RecFOFormula> + use<'a> {
        ptcl.steps()
            .iter()
            .flat_map(
                move |step @ Step {
                          id,
                          vars,
                          cond,
                          msg,
                      }| {
                    let vars = vars.iter().map(|v| RecFOFormula::Var(v.clone()));
                    let s = rexp!((id #vars*));

                    let condition = rexp!((and (HAPPENS #s) (LT #s #time)));
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
    }
}

impl crate::rules::utils::SyntaxSearcher for Search {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search_prf")
    }

    fn is_instance(&self, pbl: &Problem, fun: &Function) -> bool {
        fun == &NONCE || fun == &self.prf(pbl).hash
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[RecFOFormula],
    ) -> ControlFlow<()> {
        let Self { m, k, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((= #arg #k)));
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

decl_vars!(const M:Bitstring, K:Nonce, P:Protocol, T:Time);

#[derive(Debug)]
struct PrfVampireRule {
    prf: usize,
    pattern: Pattern<Lang>,
    exec: Rc<VampireExec>,
}

impl PrfVampireRule {
    fn new(pbl: &Problem, prf @ PRF { search_trigger, .. }: &PRF) -> Self {
        Self {
            prf: prf.index(),
            pattern: Pattern::from(&rexp!((search_trigger #M #K #P #T))),
            exec: Rc::new(VampireExec::builder().with_pbl(pbl).build()),
        }
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>> for PrfVampireRule {
    fn name(&self) -> std::borrow::Cow<'_, str> {
        format!("prf vampire #{:}", self.prf).into()
    }

    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: egg::Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) = self.pattern
                .search_eclass(egraph, goal), Dependancy::impossible());

        for subst in substs.substs {
            let [m, k, time] =
                [M, K, T].map(|x| RecFOFormula::try_from_subts(egraph, &subst, x).unwrap());
            let pbl = egraph.analysis.pbl();
            let search = Search {
                prf_idx: self.prf,
                m,
                k,
            };
            // get the protocol from the function
            let ptcl = {
                let id = subst.get(P.as_egg()).unwrap();
                let idx = egraph[*id]
                    .iter()
                    .find_map(|f| f.head.get_protocol_index())
                    .unwrap(); // there has to be one
                &pbl.protocols()[idx]
            };

            let search = search.search_timepoint(pbl, ptcl, time).collect_vec();
            let pbl = egraph.analysis.pbl_mut();
            pbl.find_temp_quantifiers(&search);
            let result = search.into_iter().all(|query| {
                let query = query.as_smt(*pbl).unwrap();
                self.exec
                    .run_to_dependancy()
                    .pbl(pbl)
                    .query(query)
                    .call()
                    .is_axioms()
            });
            pbl.clear_temp_quantifiers();
            ereturn_if!(result, Dependancy::axiom());
        }

        Dependancy::impossible()
    }
}
