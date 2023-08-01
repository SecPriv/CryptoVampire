use crate::{
    formula::{
        function::{
            signature::FixedRefSignature,
            traits::{Evaluatable, FixedSignature, MaybeEvaluatable},
            Function,
        },
        sort::Sort,
    },
    utils::vecref::VecRefClone,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct InnerBaseFunction<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    pub out: Sort<'bump>,
    pub eval_fun: Function<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub enum BaseFunction<'bump> {
    Eval(&'bump BaseFunction<'bump>),
    Base(InnerBaseFunction<'bump>),
}

impl<'bump> InnerBaseFunction<'bump> {
    pub fn eval_fun(&self) -> Function<'bump> {
        self.eval_fun
    }

    pub fn out(&self) -> Sort<'bump> {
        self.out
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }
}

pub struct BaseFunctionTuple<'bump> {
    pub main: Function<'bump>,
    pub eval: Function<'bump>,
}

impl<'bump> Evaluatable<'bump> for InnerBaseFunction<'bump> {
    fn get_evaluated(&self) -> Function<'bump> {
        self.eval_fun()
    }
}

impl<'bump> MaybeEvaluatable<'bump> for BaseFunction<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        match self {
            BaseFunction::Eval(_) => None,
            BaseFunction::Base(ibf) => ibf.maybe_get_evaluated(),
        }
    }
}

impl<'a, 'bump> FixedSignature<'a, 'bump> for InnerBaseFunction<'bump>
where
    'bump: 'a,
{
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.out(),
            args: self.args().into(),
        }
    }
}

impl<'a, 'bump> FixedSignature<'a, 'bump> for BaseFunction<'bump>
where
    'bump: 'a,
{
    fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
        match self {
            BaseFunction::Base(x) => x.as_fixed_signature(),
            BaseFunction::Eval(e) => {
                let FixedRefSignature { out, args } = e.as_fixed_signature();
                let out = out.evaluated_sort().unwrap();
                let args: Option<VecRefClone<_>> =
                    args.into_iter().map(|s| s.evaluated_sort()).collect();
                let args = args.unwrap();
                FixedRefSignature { out, args }
            }
        }
    }
}
