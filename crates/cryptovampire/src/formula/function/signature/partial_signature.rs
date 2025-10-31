use std::iter::Cloned;

use itertools::{Itertools, MapInto};
use utils::vecref::{IterVecRef, VecRef};

use super::{Impossible, Signature};
use crate::formula::sort::Sort;
use crate::formula::sort::sort_proxy::SortProxy;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct OnlyArgsSignature<'a, 'bump: 'a> {
    args: VecRef<'a, Sort<'bump>>,
    out: SortProxy<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct OnlyArgsSignatureProxy<'a, 'bump: 'a> {
    args: VecRef<'a, SortProxy<'bump>>,
    out: SortProxy<'bump>,
}

impl<'a, 'bump: 'a> OnlyArgsSignature<'a, 'bump> {
    pub fn new(args: impl Into<VecRef<'a, Sort<'bump>>>) -> Self {
        Self {
            args: args.into(),
            out: Default::default(),
        }
    }
}

impl<'a, 'bump: 'a> OnlyArgsSignatureProxy<'a, 'bump> {
    pub fn new(args: impl Into<VecRef<'a, SortProxy<'bump>>>) -> Self {
        Self {
            args: args.into(),
            out: Default::default(),
        }
    }
}

impl<'a, 'bump: 'a> Signature<'bump> for OnlyArgsSignature<'a, 'bump> {
    type Args<'b>
        = MapInto<IterVecRef<'a, 'b, Sort<'bump>>, SortProxy<'bump>>
    where
        Self: 'b,
        'bump: 'b;

    type FxSign = Impossible;

    fn out(&self) -> SortProxy<'bump> {
        self.out.clone()
    }

    fn args<'b>(&'b self) -> Self::Args<'b>
    where
        'bump: 'b,
    {
        self.args.iter().map_into()
    }

    fn fast(self) -> Option<Self::FxSign> {
        None
    }

    fn args_size(&self) -> std::ops::RangeInclusive<utils::infinity::Infinity<usize>> {
        0.into()..=(self.args.len() - 1).into()
    }
}

impl<'a, 'bump: 'a> Signature<'bump> for OnlyArgsSignatureProxy<'a, 'bump> {
    type Args<'b>
        = Cloned<IterVecRef<'a, 'b, SortProxy<'bump>>>
    where
        Self: 'b,
        'bump: 'b;

    type FxSign = Impossible;

    fn out(&self) -> SortProxy<'bump> {
        self.out.clone()
    }

    fn args<'b>(&'b self) -> Self::Args<'b>
    where
        'bump: 'b,
    {
        self.args.iter().cloned()
    }

    fn fast(self) -> Option<Self::FxSign> {
        None
    }

    fn args_size(&self) -> std::ops::RangeInclusive<utils::infinity::Infinity<usize>> {
        0.into()..=(self.args.len() - 1).into()
    }
}
