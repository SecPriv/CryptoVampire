use std::ops::RangeInclusive;

use utils::infinity::Infinity;
use utils::match_as_trait;

use super::{AsFixedSignature, Signature};
use crate::formula::sort::Sort;
use crate::formula::sort::sort_proxy::SortProxy;

#[derive(Debug)]
pub enum Lazy<A, B> {
    A(A),
    B(B),
}
impl<'bump, A, B> Signature<'bump> for Lazy<A, B>
where
    A: Signature<'bump>,
    B: Signature<'bump>,
{
    type Args<'a>
        = Lazy<<A as Signature<'bump>>::Args<'a>, <B as Signature<'bump>>::Args<'a>>
    where
        Self: 'a,
        'bump: 'a;

    type FxSign = LazyFxSignature<A::FxSign, B::FxSign>;

    fn out(&self) -> SortProxy<'bump> {
        match_as_trait!(self => {Self::A(x) | Self::B(x) => {x.out()}})
    }

    fn args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        match self {
            Lazy::A(x) => Lazy::A(x.args()),
            Lazy::B(x) => Lazy::B(x.args()),
        }
    }

    fn fast(self) -> Option<Self::FxSign> {
        match self {
            Lazy::A(x) => x.fast().map(LazyFxSignature::A),
            Lazy::B(x) => x.fast().map(LazyFxSignature::B),
        }
    }

    fn args_size(&self) -> RangeInclusive<Infinity<usize>> {
        match_as_trait!(self => {Self::A(x) | Self::B(x) => {x.args_size()}})
    }
}

#[derive(Debug)]
pub enum LazyFxSignature<A, B> {
    A(A),
    B(B),
}

impl<'bump, A, B> AsFixedSignature<'bump> for LazyFxSignature<A, B>
where
    A: AsFixedSignature<'bump>,
    B: AsFixedSignature<'bump>,
{
    type Args<'a>
        = Lazy<<A as AsFixedSignature<'bump>>::Args<'a>, <B as AsFixedSignature<'bump>>::Args<'a>>
    where
        Self: 'a,
        'bump: 'a;

    fn fixed_out(&self) -> Sort<'bump> {
        match_as_trait!(self => {Self::A(x) | Self::B(x) => {x.fixed_out()}})
    }

    fn fixed_args<'a>(&'a self) -> Self::Args<'a>
    where
        'bump: 'a,
    {
        match self {
            LazyFxSignature::A(x) => Lazy::A(x.fixed_args()),
            LazyFxSignature::B(x) => Lazy::B(x.fixed_args()),
        }
    }
}

impl<A, B, C> IntoIterator for Lazy<A, B>
where
    A: IntoIterator<Item = C>,
    B: IntoIterator<Item = C>,
{
    type Item = C;

    type IntoIter = LazyIterator<<A as IntoIterator>::IntoIter, <B as IntoIterator>::IntoIter>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Lazy::A(x) => LazyIterator::A(x.into_iter()),
            Lazy::B(x) => LazyIterator::B(x.into_iter()),
        }
    }
}

pub enum LazyIterator<A, B> {
    A(A),
    B(B),
}

impl<A, B, C> Iterator for LazyIterator<A, B>
where
    A: Iterator<Item = C>,
    B: Iterator<Item = C>,
{
    type Item = C;

    fn next(&mut self) -> Option<Self::Item> {
        match_as_trait!(self => {Self::A(x) | Self::B(x) => {x.next()}})
    }
}
