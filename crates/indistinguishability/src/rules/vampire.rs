use crate::{
    Lang, Problem,
    problem::PAnalysis,
    rexp,
    terms::{RecFOFormula, VAMPIRE},
    vampire::runner::VampireExec,
};
use bon::Builder;
use cryptovampire_smt::{IntoSmt, Smt};
use egg::{ENodeOrVar, Pattern, RecExpr, Searcher, Var};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain};
use static_init::dynamic;
use std::{io::Write, rc::Rc};
use utils::ereturn_let;

declare_trace!($"vampire_rule");

#[dynamic]
static PATTERN: Pattern<Lang> = Pattern::new(RecExpr::from(rexp!((VAMPIRE #0)).to_vec()));

static VAR: Var = Var::from_u32(0);

/// A rule that calls vampire to get its answer
#[derive(Clone, Builder)]
pub struct VampireRule {
    #[builder(into)]
    exec: Rc<VampireExec>,
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

        dbg!(s);

        let to_prove_id = s.get(VAR).unwrap();
        let to_prove = egraph.id_to_expr(*to_prove_id);
        let to_prove = RecFOFormula::from(RecExpr::from_iter(
            to_prove.into_iter().map(ENodeOrVar::ENode),
        ))
        .into_smt();

        let pbl: &mut Problem = egraph.analysis.pbl_mut();
        let prelude = pbl.get_smt_prelude();

        tr!("running on {to_prove}");

        let res = self
            .exec
            .run_smt(chain![
                prelude.iter().cloned(),
                [Smt::mk_query(to_prove), Smt::CheckSat]
            ])
            .expect("something went wrong with vampire");

        if res {
            Dependancy::axiom()
        } else {
            Dependancy::impossible()
        }
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<vampire>.")
    }
}
