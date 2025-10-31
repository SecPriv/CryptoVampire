use std::borrow::Cow;
use std::rc::Rc;

use bon::Builder;
use cryptovampire_smt::Smt;
use egg::{Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::chain;
use static_init::dynamic;
use utils::ereturn_let;

use crate::problem::PAnalysis;
use crate::runners::{SmtRunner, SmtSolver};
use crate::terms::{RecFOFormula, VAMPIRE};
use crate::{Lang, Problem, rexp};

declare_trace!($"vampire_rule");

decl_vars!(const; X);

#[dynamic]
static PATTERN: Pattern<Lang> = Pattern::from(&rexp!((VAMPIRE #X)));

/// A rule that calls vampire to get its answer
#[derive(Clone, Builder)]
pub struct VampireRule {
    #[builder(into)]
    exec: SmtRunner,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for VampireRule {
    fn search(
        &self,
        prgm: &mut golgge::Program<Lang, PAnalysis<'a>>,
        goal: egg::Id,
    ) -> golgge::Dependancy {
        ereturn_let!(let Some(m) = PATTERN.search_eclass(prgm.egraph(), goal), Default::default());
        ereturn_let!(let Some(s) = m.substs.first(), Default::default());

        let egraph = prgm.egraph_mut();

        let Some(to_prove) = RecFOFormula::try_from_subts(egraph, s, X) else {
            panic!("aaaaa");
            #[allow(unreachable_code)]
            return golgge::Dependancy::impossible();
        };
        let pbl: &mut Problem = egraph.analysis.pbl_mut();
        pbl.find_temp_quantifiers(std::slice::from_ref(&to_prove));

        let to_prove = to_prove.as_smt(pbl).unwrap();

        self.exec.run_to_dependancy(pbl, to_prove)
    }

    fn name(&self) -> std::borrow::Cow<'_, str> {
        Cow::Borrowed("vampire")
    }
}
