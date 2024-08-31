use std::marker::PhantomData;

use crate::{Bounder, Destructed, Formula, FormulaIterator};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct VariableIterator<F> {
    g: PhantomData<F>,
}

impl<F> Default for VariableIterator<F> {
    fn default() -> Self {
        Self {
            g: Default::default(),
        }
    }
}

impl<F: Formula + Clone> FormulaIterator for VariableIterator<F> {
    type F = F;

    type Passing = ();
    type U = F::Var;

    fn next<H>(&mut self, current: F, _: &(), helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = (), U = Self::U>,
    {
        let Destructed { head, args } = current.destruct();
        helper.extend_child_with_default(args);
        match head {
            crate::HeadSk::Var(v) => {
                helper.push_result(v);
            }
            _ => (),
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct DepthIterator<F> {
    g: PhantomData<F>,
}

impl<F: Formula + Clone> FormulaIterator for DepthIterator<F> {
    type F = F;

    type Passing = u32;
    type U = u32;

    fn next<H>(&mut self, current: F, passing: &u32, helper: &mut H)
    where
        H: crate::IteratorHelper<F = F, Passing = u32, U = Self::U>,
    {
        helper.push_result(*passing);
        helper.extend_child(current.args().map(|f| (f, *passing + 1)));
    }
}

pub struct BoundedVariableIterator<F>
where
    F: Formula,
{
    g: PhantomData<F>,
    bvars: Vec<<F as Formula>::Var>,
}

impl<F> FormulaIterator for BoundedVariableIterator<F>
where
    F: Formula,
    F::Quant: Bounder<F::Var>,
    F::Var: Eq + Clone,
{
    type F = F;

    type Passing = usize;

    type U = F::Var;

    fn next<H>(&mut self, current: Self::F, passing: &Self::Passing, helper: &mut H)
    where
        H: crate::IteratorHelper<F = Self::F, Passing = Self::Passing, U = Self::U>,
    {
        self.bvars.truncate(*passing);
        let Destructed { head, args } = current.destruct();
        match head {
            crate::HeadSk::Var(v) => {
                if self.bvars.contains(&v) {
                    helper.push_result(v);
                }
            }
            crate::HeadSk::Fun(_) => {
                helper.extend_child_same_passing(args, passing);
            }
            crate::HeadSk::Quant(q) => {
                self.bvars.extend(q.bounds());
                let passing = self.bvars.len();
                helper.extend_child(args.map(|f| (f, passing)));
            }
        }
    }
}

impl<F: Formula> Default for BoundedVariableIterator<F> {
    fn default() -> Self {
        Self {
            g: Default::default(),
            bvars: Default::default(),
        }
    }
}
