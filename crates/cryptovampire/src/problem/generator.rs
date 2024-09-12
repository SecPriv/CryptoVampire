use crate::{
    environement::environement::Environement,
    formula::file_descriptior::{axioms::Axiom, declare::Declaration},
};

use super::problem::Problem;

pub trait Generator<'bump> {
    fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    );
}
