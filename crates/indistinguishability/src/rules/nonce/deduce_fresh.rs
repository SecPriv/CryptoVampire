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
use crate::rules::utils::EgraphSearcher;
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

        let condition = substs.substs.iter().map(|subst| {
            let [nonce, content, hypothesis] =
                [NONCE_VAR, CONTENT, HYPOTHESIS].map(|i| *subst.get(i.as_egg()).unwrap());
            let hypothesis = RecFOFormula::try_from_id(egraph, hypothesis).unwrap();
            let nonce = Nonce::builder().content_id(egraph, nonce).build();

            let builder = RefFormulaBuilder::builder().and().build();
            nonce.search_egraph(
                egraph,
                &builder,
                content,
                &Default::default(),
                &Default::default(),
            );
            let search = builder.into_inner().unwrap().into_formula();

            hypothesis >> search
        });
        let query = rexp!((or #condition*));
        tr!("checking {query}");
        let pbl: &mut Problem = egraph.analysis.pbl_mut();

        pbl.find_temp_quantifiers(&[query.clone()]);

        let query = query.as_smt(pbl).unwrap();
        tr!("checking {query}");

        self.exec
            .run_to_dependancy()
            .pbl(pbl)
            .query(query)
            .clean_afterward()
            .call()
    }

    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fresh nonce")
    }
}
