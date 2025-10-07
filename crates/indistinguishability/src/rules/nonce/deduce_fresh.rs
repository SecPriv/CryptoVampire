use std::borrow::Cow;
use std::rc::Rc;

use bon::Builder;
use cryptovampire_smt::{IntoSmt, SmtFormula};
use egg::{Id, Pattern, Searcher, Var};
use golgge::{Dependancy, Rule};
use static_init::dynamic;
use utils::ereturn_let;

use super::*;
use crate::problem::PAnalysis;
use crate::rules::utils::fresh::RefFormulaBuilder;
use crate::terms::{FRESH_NONCE, Variable};
use crate::vampire::runner::VampireExec;
use crate::{Lang, Problem, fresh, rexp};

decl_vars!(const; NONCE_VAR, CONTENT, HYPOTHESIS);

#[dynamic]
static FRESH_NONCE_PATTERN: Pattern<Lang> =
    Pattern::from(&rexp!((FRESH_NONCE #NONCE_VAR #CONTENT #HYPOTHESIS)));

#[derive(Clone, Builder)]
pub struct FreshNonce {
    #[builder(into)]
    exec: Rc<VampireExec>,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for FreshNonce {
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        assert_eq!(NONCE_VAR, CONTENT);

        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) =  FRESH_NONCE_PATTERN.search_eclass(egraph, goal),Dependancy::impossible());

        let mut conditions = Vec::with_capacity(substs.substs.len());
        for subst in substs.substs {
            let [nonce, content, hypothesis] =
                [0, 1, 2].map(|i| *subst.get(Var::from_usize(i)).unwrap());
            let hypothesis = convert_id(egraph, hypothesis);
            let nonce = Nonce::builder().content_id(egraph, nonce).build();

            let builder = RefFormulaBuilder::builder().and().build();
            nonce.search_egraph(egraph, builder.clone(), content, Default::default());
            let search = builder.into_inner().unwrap().into_formula();

            conditions.push((hypothesis >> search).into_smt())
        }
        let condition = SmtFormula::Or(conditions);

        tr!("checking {condition}");
        let pbl: &mut Problem = egraph.analysis.pbl_mut();

        self.exec.run_to_dependancy(pbl, condition)
    }

    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fresh nonce")
    }
}
