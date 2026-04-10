use std::borrow::Cow;

use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, PrologRule, Rule};
use itertools::Itertools;
use static_init::dynamic;
use utils::{ereturn_if, ereturn_let};

use super::*;
use crate::libraries::utils::formula_builder::RefFormulaBuilder;
use crate::libraries::utils::{RuleSink, SyntaxSearcher};
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::runners::SmtRunner;
use crate::terms::{
    AND, BITE, BOUND_ANDS, FRESH_NONCE, FRESH_NONCE_TRIGGER, FRESH_NONCE_TRIGGER_MEM, Formula,
    Function, HAPPENS, LEQ, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MEMORY_CELL,
    MACRO_MSG, MITE, NONCE, PRED, Sort, UNFOLD_COND, UNFOLD_MSG, VAMPIRE,
};
use crate::{CVProgram, Lang, Problem, fresh, rexp};

decl_vars!(const; N:Nonce, T:Time, P:Protocol, H:Bool, M:Nonce, C:Bool, L, R, CELL:MemoryCell);

#[dynamic]
static TRIGGER_PATTERN: Pattern<Lang> = Pattern::from(&rexp!((FRESH_NONCE_TRIGGER #N #T #P #H)));

#[dynamic]
static TRIGGER_PATTERN_MEM: Pattern<Lang> =
    Pattern::from(&rexp!((FRESH_NONCE_TRIGGER_MEM #N #T #P #H #CELL)));

/// A rule that deduces the freshness of a nonce
#[derive(Clone, Builder)]
pub struct FreshNonce {
    /// The SMT runner to use for executing SMT queries.
    #[builder(into)]
    exec: SmtRunner,
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for FreshNonce {
    /// Searches for patterns related to fresh nonces in the e-graph and deduces their freshness.
    ///
    /// This method now looks for `(FRESH_NONCE_TRIGGER #N #T #P #H)` patterns, which are produced
    /// by prolog rules when encountering macros like `frame` or `exec`.
    /// It then constructs a logical query to check if the nonce is fresh across protocol steps
    /// up to the given timepoint.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        // Handle regular triggers (MACRO_FRAME, MACRO_EXEC, MACRO_INPUT)
        if let Some(substs) = TRIGGER_PATTERN.search_eclass(prgm.egraph(), goal) {
            for subst in substs.substs {
                let [n, t, h] = [N, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = Nonce::builder()
                    .content(n)
                    .build()
                    .search_id_timepoint(prgm, &self.exec, p, t, h)
                    .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }

        // Handle MACRO_MEMORY_CELL trigger
        if let Some(substs) = TRIGGER_PATTERN_MEM.search_eclass(prgm.egraph(), goal) {
            for subst in substs.substs {
                let [n, t, h, cell, p] = [N, T, H, CELL, P].map(|x| {
                    Formula::try_from_id(prgm.egraph(), *subst.get(x.as_egg()).unwrap()).unwrap()
                });

                let nonce_searcher = Nonce::builder().content(n).build();
                let mem_cell_term = rexp!((MACRO_MEMORY_CELL #cell (PRED #t) #p));
                let result = nonce_searcher
                    .search_term(prgm, &self.exec, mem_cell_term, h)
                    .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }

        Dependancy::impossible()
    }

    /// Returns the name of this rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fresh nonce dynamic")
    }
}

/// Adds static prolog rules for decomposing `FRESH_NONCE` goals.
pub fn mk_static_rules(pbl: &Problem, sink: &mut impl RuleSink) {
    let functions = pbl
        .functions()
        .iter_current()
        .filter(|f| f.is_nonce() || !f.is_special_subterm())
        .filter(|f| !f.is_out_of_term_algebra())
        .filter(|f| f != &&NONCE && f != &&AND && f != &&MITE && f != &&BITE)
        .sorted_by_key(|f| f.arity())
        .cloned();

    sink.extend_rules(mk_many_prolog! {
    // Base case: Nonce constructor
        "fresh_nonce_nonce" :
        (FRESH_NONCE #N (NONCE #M) #H) :-
            (VAMPIRE (=> #H (distinct #N #M))).

    // Macros triggers
        "fresh_nonce_frame" :
            (FRESH_NONCE #N (MACRO_FRAME #T #P) #H) :-
                (FRESH_NONCE_TRIGGER #N #T #P #H).

        "fresh_nonce_exec":
            (FRESH_NONCE #N (MACRO_EXEC #T #P) #H) :-
                (FRESH_NONCE_TRIGGER #N #T #P #H).

        "fresh_nonce_input":
            (FRESH_NONCE #N (MACRO_INPUT #T #P) #H) :-
                (FRESH_NONCE_TRIGGER #N (PRED #T) #P #H).

        "fresh_nonce_memory_cell":
            (FRESH_NONCE #N (MACRO_MEMORY_CELL #CELL (PRED #T) #P) #H) :-
                (FRESH_NONCE_TRIGGER_MEM #N (PRED #T) #P #H #CELL).

    // Unfolding rules for MSG and COND
        "fresh_nonce_msg":
            (FRESH_NONCE #N (MACRO_MSG #T #P) #H) :-
                (VAMPIRE (=> #H (HAPPENS #T))),
                (FRESH_NONCE #N (UNFOLD_MSG #T #P) #H).

        "fresh_nonce_cond":
            (FRESH_NONCE #N (MACRO_COND #T #P) #H) :-
                (VAMPIRE (=> #H (HAPPENS #T))),
                (FRESH_NONCE #N (UNFOLD_COND #T #P) #H).

    // if-then-else
        "fresh_nonce_ite_m":
            (FRESH_NONCE #N (MITE #C #L #R) #H) :-
                (BOUND_ANDS #C #H),
                (BOUND_ANDS (not #C) #H),
                (FRESH_NONCE #N #C #H),
                (FRESH_NONCE #N #L (and #C #H)),
                (FRESH_NONCE #N #R (and (not #C) #H)).

        "fresh_nonce_ite_b":
            (FRESH_NONCE #N (BITE #C #L #R) #H) :-
                (BOUND_ANDS #C #H),
                (BOUND_ANDS (not #C) #H),
                (FRESH_NONCE #N #C #H),
                (FRESH_NONCE #N #L (and #C #H)),
                (FRESH_NONCE #N #R (and (not #C) #H)).

    // AND
        "fresh_nonce_and":
        (FRESH_NONCE #N (AND #C #L) #H) :-
            (BOUND_ANDS #C #H),
            (FRESH_NONCE #N #C #H),
            (FRESH_NONCE #N #L (and #C #H)).
    });

    // Decompose regular functions
    for f in functions {
        sink.add_rule(mk_rule_one(&f));
    }
}

fn mk_rule_one(fun: &Function) -> PrologRule<Lang> {
    let args = fun
        .signature
        .inputs
        .iter()
        .map(|&s| Formula::Var(fresh!(s)))
        .collect_vec();

    let deps = args
        .iter()
        .filter(|v| [Sort::Bool, Sort::Bitstring].contains(&v.try_get_sort().unwrap()))
        .map(|arg| Pattern::from(&rexp!((FRESH_NONCE #N #arg #H))))
        .collect_vec();

    let input = Pattern::from(&rexp!((FRESH_NONCE #N (fun #args*) #H)));

    PrologRule::builder()
        .input(input)
        .deps(deps)
        .name(format!("fresh_nonce_{fun}"))
        .build()
        .unwrap()
}
