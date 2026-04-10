use std::borrow::Cow;
use std::collections::HashSet;

use egg::{Analysis, EGraph, Id, Pattern, SearchMatches, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use rustc_hash::FxHashSet;
use static_init::dynamic;
use utils::{econtinue_if, ereturn_let};

use crate::libraries::Library;
use crate::problem::{PAnalysis, RcRule};
use crate::terms::{AND, BOUND_ANDS, FAIL};
use crate::{Lang, rexp};

decl_vars!(const; A:Bool, B:Bool);

#[dynamic]
pub static PATTERN: Pattern<Lang> = Pattern::from(&rexp!((BOUND_ANDS #A #B)));

pub struct AndBounderLib;

impl Library for AndBounderLib {
    fn add_rules(&self, _: &mut crate::Problem, sink: &mut impl super::utils::RuleSink) {
        sink.extend_rules([
            mk_prolog!(
              "bound and true" ; a : (BOUND_ANDS true #a) :- !, FAIL
            ),
            mk_prolog!(
              "bound and self" ; a : (BOUND_ANDS #a #a) :- !, FAIL
            ),
        ]);

        sink.add_rule(AndBounder);
    }
}

// TODO: add the `Bound and` guard in front of every and and if rules. This
// breaks substitution reconstruction from proofs though...

/// This rules guards against looping over ands by giving up when it notices
/// that things will loop
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct AndBounder;

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for AndBounder {
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("and bounder")
    }
    fn search(
        &self,
        prgm: &mut golgge::Program<Lang, PAnalysis<'a>, RcRule>,
        goal: egg::Id,
    ) -> golgge::Dependancy {
        // {
        //     for SearchMatches { eclass, .. } in PATTERN.search(prgm.egraph()) {
        //         prgm.forget(eclass);
        //     }
        // }

        ereturn_let!(let Some(substs) = PATTERN.search_eclass(prgm.egraph(), goal), Dependancy::impossible());

        let mut todo = Vec::new();
        let mut seena: HashSet<_, _> = Default::default();
        let mut seenb: HashSet<_, _> = Default::default();

        for subst in substs.substs {
            todo.clear();
            seena.clear();
            seenb.clear();
            let egraph = prgm.egraph();
            let [a, b] = [A, B].map(|x| *subst.get(x.as_egg()).unwrap());

            todo.push(b);
            and_set(egraph, &mut todo, &mut seenb);
            debug_assert!(todo.is_empty());
            todo.push(a);
            and_set(egraph, &mut todo, &mut seena);

            if seena
                .difference(&seenb)
                .flat_map(|id| egraph[*id].iter())
                .all(|l| l.head == AND)
            {
                return Dependancy::impossible();
            }
        }

        Dependancy::axiom()
    }
}

fn and_set<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    todo: &mut Vec<Id>,
    seen: &mut FxHashSet<Id>,
) {
    while let Some(id) = todo.pop() {
        econtinue_if!(seen.contains(&id));
        for Lang { head, args } in egraph[id].iter() {
            econtinue_if!(head != &AND);
            let (a, b) = args.iter().collect_tuple().unwrap();
            todo.push(*a);
            todo.push(*b);
        }
        seen.insert(id);
    }
}
