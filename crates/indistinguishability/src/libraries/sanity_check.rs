use std::borrow::Cow;

use golgge::{Dependancy, Rule};

use crate::problem::{PAnalysis, RcRule};
use crate::{CVProgram, Lang};

/// A rule that performs basic sanity checks on the e-graph.
///
/// This rule checks for contradictions like `true = false` within the e-graph.
pub struct SanityCheck;

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for SanityCheck {
    /// Performs a sanity check by looking for `true = false` in the e-graph.
    ///
    /// If such a contradiction is found, it panics and prints an explanation.
    fn search(&self, pblm: &mut CVProgram<'a>, _: egg::Id) -> golgge::Dependancy {
        let egraph = pblm.egraph_mut();

        use crate::terms::{FALSE, TRUE};

        let mtrue = TRUE.app_empty();
        let mfalse = FALSE.app_empty();
        let x = egraph.equivs(&mtrue, &mfalse);
        if !x.is_empty() {
            eprintln!("true = false");
            eprintln!(
                "{}",
                egraph
                    .explain_equivalence(&mtrue, &mfalse)
                    .get_flat_string()
            );
            panic!("wtf")
        }

        Dependancy::impossible()
    }

    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("sanity check")
    }
}
