use anyhow::ensure;
use itertools::{chain, Itertools};
use utils::implvec;

use crate::{
    formula::{formula::ARichFormula, quantifier::Quantifier, sort::builtins::STEP, variable::Variable},
    problem::step::Step,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ordering<'bump> {
    quantifier: Quantifier<'bump>,
    kind: OrderingKind<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OrderingKind<'bump> {
    LT(ARichFormula<'bump>, ARichFormula<'bump>),
    Exclusive(ARichFormula<'bump>, ARichFormula<'bump>),
}


impl<'bump> Ordering<'bump> {
    pub fn new(vars: Quantifier<'bump>, kind: OrderingKind<'bump>) -> Self {
        Self { quantifier: vars, kind }
    }
    
    pub fn check(&self
    ) -> anyhow::Result<()> {
        let vars = self.quantifier().get_variables().as_ref();
        for f in self.formulas() {
            ensure!(
                f.get_free_vars().iter().all(|v| vars.contains(v)),
                "{f:} contains variables not it vars [{}]",
                vars.iter().map(|v| format!("{v:}")).join(", ")
            );
            ensure!(f.sort() == Some(STEP.clone()), "{f:} is not of sort step")
        }
        Ok(())
    }

    pub fn kind(&self) -> &OrderingKind<'bump> {
        &self.kind
    }

    pub fn formulas<'a>(&'a self) -> impl Iterator<Item = &'a ARichFormula<'bump>> {
        match self.kind() {
            OrderingKind::LT(l, r) => [l, r],
            OrderingKind::Exclusive(l, r) => [l, r],
        }
        .into_iter()
    }
    
    pub fn quantifier(&self) -> &Quantifier<'bump> {
        &self.quantifier
    }
}
