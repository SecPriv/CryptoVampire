use std::borrow::Cow;

use bon::Builder;
use egg::{Pattern, Searcher};
use golgge::Rule;
use static_init::dynamic;
use utils::ereturn_let;

use crate::problem::{PAnalysis, RcRule};
use crate::runners::SmtRunner;
use crate::terms::{Formula, VAMPIRE};
use crate::{CVProgram, Lang, Problem, rexp};

declare_trace!($"vampire_rule");

decl_vars!(const; X);

#[dynamic]
static PATTERN: Pattern<Lang> = Pattern::from(&rexp!((VAMPIRE #X)));

/// A rule that calls vampire to get its answer
#[derive(Clone, Builder)]
pub struct VampireRule {
    /// The SMT runner to use
    #[builder(into)]
    exec: SmtRunner,
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for VampireRule {
    /// Searches for patterns in the e-graph and calls the Vampire SMT solver if a match is found.
    ///
    /// This method looks for `(VAMPIRE #X)` patterns. If found, it extracts the formula `#X`,
    /// translates it to an SMT formula, and sends it to the configured SMT runner (`exec`).
    /// The result from the SMT solver determines the dependency returned.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: egg::Id) -> golgge::Dependancy {
        ereturn_let!(let Some(m) = PATTERN.search_eclass(prgm.egraph(), goal), Default::default());
        ereturn_let!(let Some(s) = m.substs.first(), Default::default());

        let egraph = prgm.egraph_mut();

        let to_prove = Formula::try_from_id(egraph, *s.get(X.as_egg()).unwrap()).unwrap();
        let pbl: &mut Problem = egraph.analysis.pbl_mut();
        pbl.find_temp_quantifiers(std::slice::from_ref(&to_prove));

        let to_prove = to_prove.as_smt(pbl).unwrap();

        // if dep.is_axioms() { <- not possible likely because of indices reuse
        //     let et = egraph.add(TRUE.app_id([]));
        //     egraph.union_trusted(*s.get(X.as_egg()).unwrap(), et, "v");
        // }

        self.exec.run_to_dependancy(pbl, to_prove)
    }

    /// Returns the name of this rule.
    fn name(&self) -> std::borrow::Cow<'_, str> {
        Cow::Borrowed("vampire")
    }
}
