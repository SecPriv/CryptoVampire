use std::rc::Rc;

use cryptovampire_smt::{IntoSmt, Smt, SmtFormula};
use egg::{Analysis, EGraph, ENodeOrVar, Pattern, PatternAst, RecExpr, Searcher, Var, VarExposed};
use golgge::{Dependancy, PrologRule, Rule};
use itertools::{Itertools, chain, izip};
use logic_formula::{Destructed, Formula, HeadSk, egg::SimpleDiscriminant};
use utils::{ereturn_if, ereturn_let, implvec};

use crate::{
    problem::{PAnalysis, PRule, RcRule}, protocol::{Protocol, Step}, rexp, rules::{
        prf::search, utils::{
            fresh::{Condition, Mode, RefFormulaBuilder}, SyntaxSearcher
        }, PRF
    }, terms::{
        formula_utils::offsets_owned, Alias, AliasRewrite, Exists, FOBinder, Function, RecFOFormula, Sort, EQ, FAIL, HAPPENS, LT, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_MSG, NONCE, VAMPIRE
    }, vampire::runner::VampireExec, Lang, LangVar, Problem
};

declare_trace!($"search_prf");

// =========================================================
// ==================== prolog search ======================
// =========================================================

pub fn mk_rules<'a>(pbl: &'a Problem, prf: &'a PRF) -> impl Iterator<Item = RcRule> + use<'a> {
    let functions = pbl
        .function
        .iter()
        .filter(|f| f != &&NONCE)
        .filter(|f| matches!(f.signature.output, Sort::Bitstring | Sort::Bool))
        .filter(|f| !f.is_special_subterm())
        .cloned();

    let prolog_rules = chain![
        [
            mk_rule_found_instance(prf),
            mk_rule_found_key(prf),
            mk_rule_nonce(prf),
        ],
        functions.map(|f| mk_rule_one(prf, f)),
        [mk_rule_neq_m(prf), mk_rule_neq_k(prf), mk_rule_exec(prf), mk_rule_frame(prf)],
    ];

    chain![prolog_rules.map(|p| p.into_mrc())]
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
    let search = prf.get_search(fun.signature.output).unwrap();

    // the xs
    let vars: Vec<[LangVar; 1]> = fun
        .signature
        .inputs
        .iter()
        .enumerate()
        .map(|(i, _)| Var::from_u32(i as u32))
        .map(ENodeOrVar::Var)
        .map(|x| [x])
        .collect();
    let [m, k] = [1, 2]
        .map(|x| x + vars.len() as u32)
        .map(Var::from_u32)
        .map(ENodeOrVar::Var)
        .map(|x| [x]);

    let input: PatternAst<_> = search.app_var([&m, &k, fun.app_var(&vars).as_ref()].as_ref());

    let deps = izip!(fun.signature.inputs.iter(), &vars)
        .filter_map(|(&s, x)| prf.get_search(s).map(|search| (search, x)))
        .map(|(search_x, x)| search_x.app_var([&m, &k, x].as_ref()))
        .map_into();

    PrologRule::builder()
        .input(input.into())
        .deps(deps)
        .name(format!("search_prf_{fun}"))
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (NONCE #3)))).into())
        .deps(
            [rexp!((VAMPIRE (distinct #2 #3))).to_vec()]
                .map(PatternAst::from)
                .map(Pattern::from),
        )
        .name("search_prf_nonce")
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (hash #1 (NONCE #2))))).into())
        .name("search_prf_found_instance")
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (NONCE #2)))).into())
        .cut(true)
        .deps([PatternAst::from_iter(rexp!(FAIL)).into()])
        .name("search_prf_found_key")
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (hash #3 (NONCE #2))))).into())
        .deps(
            [
                rexp!((VAMPIRE (distinct #1 #3))).to_vec(),
                rexp!((search #1 #2 #3)).to_vec(),
            ]
            .map(PatternAst::from)
            .map(Pattern::from),
        )
        .name("search_prf_neq_m")
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (hash #3 (NONCE #4))))).into())
        .deps(
            [
                rexp!((VAMPIRE (distinct #2 #4))).to_vec(),
                rexp!((search #1 #2 #3)).to_vec(),
                rexp!((search #1 #2 #4)).to_vec(),
            ]
            .map(PatternAst::from)
            .map(Pattern::from),
        )
        .name("search_prf_neq_k")
        .build()
}

/// deep search on `exec`
///
/// ```text
///  search(m, k, p, t)
/// --------------------
///  m, k ||> exec(p)@t
/// ```
/// 
/// **NB**: there is no distinction between `exec` and `frame`, they both search
/// everywhere
fn mk_rule_exec(
    PRF {
        search_bool: search,
        search_trigger,
        ..
    }: &PRF,
) -> PrologRule<Lang> {
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (MACRO_EXEC #4 #3)))).into())
        .deps([PatternAst::from(rexp!((search_trigger #1 #2 #3 #4)).to_vec()).into()])
        .name("search_prf_exec")
        .build()
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
    PrologRule::builder()
        .input(PatternAst::from_iter(rexp!((search #1 #2 (MACRO_FRAME #4 #3)))).into())
        .deps([PatternAst::from(rexp!((search_trigger #1 #2 #3 #4)).to_vec()).into()])
        .name("search_prf_exec")
        .build()
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
    pub fn clone_m(&self) -> RecFOFormula {
        self.m.clone()
    }

    pub fn clone_k(&self) -> RecFOFormula {
        self.k.clone()
    }

    #[inline]
    fn prf<'a>(&self, pbl: &'a Problem) -> &'a PRF {
        pbl.cryptography()[self.prf_idx].as_prf().unwrap()
    }

    pub fn search_timepoint(
        &self,
        pbl: &Problem,
        ptcl: &Protocol,
        time: RecFOFormula,
    ) -> RecFOFormula {
        let builder = RefFormulaBuilder::new(Mode::And, None);

        for Step {
            id,
            vars,
            cond,
            msg,
        } in ptcl.steps()
        {
            // build the condition object
            let condition = {
                let named = id.rapp(vars.iter().map(|v| RecFOFormula::Var(*v)));
                let happend_cond = HAPPENS.rapp([named.clone()]);
                let lt_cond = LT.rapp([named.clone(), time.clone()]);

                let condition = happend_cond & lt_cond;
                Condition {
                    condition,
                    variables: vars.clone(),
                    sorts: id.signature.inputs_iter().collect(),
                    quantifier: FOBinder::Forall,
                }
            };

            let builder = builder.add_node(Mode::And, Some(condition));
            self.inner_search_recexpr(pbl, &builder, cond);
            self.inner_search_recexpr(pbl, &builder, msg);
        }

        builder.into_inner().unwrap().into_formula()
    }
}

impl crate::rules::utils::SyntaxSearcher for Search {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        "search_prf".into()
    }

    fn is_instance(&self, pbl: &Problem, fun: &Function) -> bool {
        fun == &NONCE || fun == &self.prf(pbl).hash
    }

    fn process_instance<'a>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(&'a [LangVar]),
    ) {
        let mut args = args.into_iter();
        if fun == NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            let content = !EQ.rapp([arg.into(), self.clone_k()]);
            builder.add_leaf(content);
        } else if fun == self.prf(pbl).hash {
            tr!("found hash!");
            let (m2, k2) = args
                .collect_tuple()
                .expect("wrong parameters given to a hash");
            let content = (!EQ.rapp([NONCE.rapp([k2.into()]), self.clone_k()]))
                & (!EQ.rapp([m2.into(), self.clone_m()]));
            builder.add_leaf(content);
            self.inner_search_recexpr(pbl, builder, m2);
            self.inner_search_recexpr(pbl, builder, k2);
        } else {
            assert!(!self.is_instance(pbl, &fun));
            unreachable!()
        }
    }
}

// =========================================================
// ======================== Rule ===========================
// =========================================================

#[derive(Debug)]
struct PrfRule {
    prf: usize,
    pattern: Pattern<Lang>,
    exec: Rc<VampireExec>,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for PrfRule {
    fn search(
        &self,
        prgm: &mut golgge::Program<Lang, PAnalysis<'a>>,
        goal: egg::Id,
    ) -> golgge::Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) = self.pattern
                .search_eclass(egraph, goal), Dependancy::impossible());
        let conditions;
        {
            let pbl = egraph.analysis.pbl();
            let c_iter = substs
                .substs
                .into_iter()
                .map(|subst| {
                    let [m, k, ptcl, time] =
                        [0, 1, 2, 3].map(|i| *subst.get(Var::from_u32(i)).unwrap());
                    let [m, k, time] =
                        [m, k, time].map(|x| RecFOFormula::try_from_id(egraph, x).unwrap());

                    let search = Search {
                        prf_idx: self.prf,
                        m,
                        k,
                    };
                    // get the protocol from the function
                    let ptcl = {
                        let idx = egraph[ptcl]
                            .iter()
                            .find_map(|f| f.head.get_protocol_index())
                            .unwrap(); // there has to be one
                        &pbl.protocols()[idx]
                    };

                    search.search_timepoint(pbl, ptcl, time)
                })
                .map(|x| x.into_smt());
            conditions = SmtFormula::Or(c_iter.collect())
        }

        let pbl: &mut Problem = egraph.analysis.pbl_mut();

        self.exec.run_to_dependancy(pbl, conditions)
    }
}
