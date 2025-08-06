use std::borrow::Cow;

use egg::Analysis;
use golgge::{Dependancy, Rule};

use crate::Lang;

pub struct SanityCheck;

impl<N: Analysis<Lang>> Rule<Lang, N> for SanityCheck {
    fn search(&self, pblm: &mut golgge::Program<Lang, N>, _: egg::Id) -> golgge::Dependancy {
        let egraph = pblm.egraph_mut();
        use logic_formula::egg::SimpleDiscriminant;

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
