use std::borrow::Cow;

use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use static_init::dynamic;
use utils::ereturn_let;

use super::*;
use crate::libraries::utils::EgraphSearcher;
use crate::libraries::utils::fresh::RefFormulaBuilder;
use crate::problem::{PAnalysis, RcRule};
use crate::runners::SmtRunner;
use crate::terms::{FRESH_NONCE, Formula};
use crate::{CVProgram, Lang, Problem, rexp};

decl_vars!(const; NONCE_VAR, CONTENT, HYPOTHESIS);

#[dynamic]
static FRESH_NONCE_PATTERN: Pattern<Lang> =
    Pattern::from(&rexp!((FRESH_NONCE #NONCE_VAR #CONTENT #HYPOTHESIS)));

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
    /// This method looks for `(FRESH_NONCE #NONCE_VAR #CONTENT #HYPOTHESIS)` patterns.
    /// It then constructs a logical query to check if the nonce is fresh under the given hypothesis
    /// and sends it to the SMT solver. The result determines the dependency returned.
    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        // assert_eq!(NONCE_VAR, CONTENT);

        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) =  FRESH_NONCE_PATTERN.search_eclass(egraph, goal),Dependancy::impossible());

        let condition = substs.substs.iter().map(|subst| {
            let [nonce, content, hypothesis] =
                [NONCE_VAR, CONTENT, HYPOTHESIS].map(|i| *subst.get(i.as_egg()).unwrap());
            let hypothesis = Formula::try_from_id(egraph, hypothesis).unwrap();
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

        pbl.find_temp_quantifiers(std::slice::from_ref(&query));

        let query = query.as_smt(pbl).unwrap();

        self.exec.run_to_dependancy(pbl, query)
    }

    /// Returns the name of this rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fresh nonce")
    }
}
