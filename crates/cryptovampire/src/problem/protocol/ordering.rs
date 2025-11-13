use std::fmt::Display;

use itertools::Itertools;
use logic_formula::AsFormula;

use crate::ensure;
use crate::error::{Location, LocationProvider};
use crate::formula::formula::ARichFormula;
use crate::formula::quantifier::Quantifier;
use crate::formula::sort::builtins::STEP;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Ordering<'bump> {
    quantifier: Quantifier<'bump>,
    kind: OrderingKind<'bump>,
    guard: ARichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum OrderingKind<'bump> {
    LT(ARichFormula<'bump>, ARichFormula<'bump>),
    Exclusive(ARichFormula<'bump>, ARichFormula<'bump>),
}

impl<'bump> Ordering<'bump> {
    pub fn new(vars: Quantifier<'bump>, kind: OrderingKind<'bump>) -> Self {
        Self::new_guarded(vars, kind, Default::default())
    }

    pub fn new_guarded(
        vars: Quantifier<'bump>,
        kind: OrderingKind<'bump>,
        guard: ARichFormula<'bump>,
    ) -> Self {
        Self {
            quantifier: vars,
            kind,
            guard,
        }
    }

    pub fn check(&self) -> crate::Result<()> {
        let vars = self.quantifier().get_variables().as_ref();
        for f in self.formulas() {
            ensure!(
                self,
                f.free_vars_iter().all(|v| vars.contains(&v)),
                "{f:} contains variables not it vars [{}]",
                vars.iter().map(|v| format!("{v:}")).join(", ")
            )?;
            ensure!(self, f.sort() == Some(*STEP), "{f:} is not of sort step")?
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

    pub fn guard(&self) -> &ARichFormula<'bump> {
        &self.guard
    }
}

impl<'bump> Display for OrderingKind<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OrderingKind::LT(l, r) => write!(f, "{l} < {r}"),
            OrderingKind::Exclusive(l, r) => write!(f, "{l} <> {r}"),
        }
    }
}

impl<'bump> Display for Ordering<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} ({}) => {}",
            self.quantifier(),
            self.guard(),
            self.kind()
        )
    }
}

impl<'a, 'bump> LocationProvider for &'a Ordering<'bump> {
    fn provide(self) -> crate::error::Location {
        Location::from_display(self)
    }
}
