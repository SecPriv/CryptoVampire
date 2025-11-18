use std::fmt::{Debug, Display};

use crate::outers::OwnedIter;
use crate::{AsFormula, Bounder, Destructed, FormulaIterator};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct UsedVariableIterator;

impl UsedVariableIterator {
    pub fn with<F: AsFormula>(
        formulas: impl IntoIterator<Item = F>,
    ) -> impl Iterator<Item = F::Var> {
        OwnedIter::new(
            formulas
                .into_iter()
                .map(|f| (f, ()))
                .map(Into::into)
                .collect(),
            UsedVariableIterator,
        )
    }
}

impl<F: AsFormula> FormulaIterator<F> for UsedVariableIterator {
    type Passing = ();
    type U = F::Var;

    fn next<H>(&mut self, current: F, _: (), helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = (), U = Self::U>,
    {
        let Destructed { head, args } = current.destruct();
        helper.extend_child_with_default(args);
        if let crate::HeadSk::Var(v) = head {
            helper.push_result(v);
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DepthIterator;

impl<F: AsFormula> FormulaIterator<F> for DepthIterator {
    type Passing = u32;
    type U = u32;

    fn next<H>(&mut self, current: F, passing: u32, helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = u32, U = Self::U>,
    {
        helper.push_result(passing);
        helper.extend_child(current.args().map(|f| (f, passing + 1)));
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct FreeVariableIterator<Var> {
    bvars: Vec<Var>,
}

impl<F> FormulaIterator<F> for FreeVariableIterator<F::Var>
where
    F: AsFormula,
    F::Quant: Bounder<F::Var>,
    F::Var: Eq + Clone,
{
    type Passing = usize;

    type U = F::Var;

    fn next<H>(&mut self, current: F, passing: Self::Passing, helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = Self::Passing, U = Self::U>,
    {
        self.bvars.truncate(passing);
        let Destructed { head, args } = current.destruct();
        match head {
            crate::HeadSk::Var(v) => {
                if !self.bvars.contains(&v) {
                    helper.push_result(v);
                }
            }
            crate::HeadSk::Fun(_) => {
                helper.extend_child_same_passing(args, &passing);
            }
            crate::HeadSk::Quant(q) => {
                self.bvars.extend(q.bounds());
                let passing = self.bvars.len();
                helper.extend_child(args.map(|f| (f, passing)));
            }
        }
    }
}

impl<V> Default for FreeVariableIterator<V> {
    fn default() -> Self {
        Self {
            bvars: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct AllTermsIterator;

impl<F: AsFormula + Clone> FormulaIterator<F> for AllTermsIterator {
    type Passing = ();
    type U = F;

    fn next<H>(&mut self, current: F, _passing: Self::Passing, helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = Self::Passing, U = Self::U>,
    {
        helper.push_result(current.clone());
        helper.extend_child_with_default(current.args());
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct QuantiferIterator;

impl<'a, F> FormulaIterator<&'a F> for QuantiferIterator
where
    &'a F: AsFormula + Debug,
{
    type Passing = ();

    type U = &'a F;

    fn next<H>(&mut self, current: &'a F, _: Self::Passing, helper: &mut H)
    where
        H: crate::IteratorHelper<F = &'a F, Passing = Self::Passing, U = Self::U>,
    {
        let Destructed { head, args } = current.destruct();
        helper.extend_child_same_passing(args, &());
        if let crate::HeadSk::Quant(_) = head {
            helper.push_result(current);
        }
    }
}
