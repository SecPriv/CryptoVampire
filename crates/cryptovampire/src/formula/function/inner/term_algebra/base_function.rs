use utils::assert_variance;

use crate::formula::function::Function;
use crate::formula::function::signature::FixedRefSignature;
use crate::formula::function::traits::{Evaluatable, FixedSignature};
use crate::formula::sort::Sort;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct BaseFunction<'bump> {
    pub name: Box<str>,
    pub args: Box<[Sort<'bump>]>,
    pub out: Sort<'bump>,
    pub eval_fun: Function<'bump>,
}

assert_variance!(BaseFunction);

impl<'bump> BaseFunction<'bump> {
    pub fn eval_fun(&self) -> Function<'bump> {
        self.eval_fun
    }

    pub fn out(&self) -> Sort<'bump> {
        self.out
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn name(&self) -> &str {
        &self.name
    }
}

pub struct BaseFunctionTuple<'bump> {
    pub main: Function<'bump>,
    pub eval: Function<'bump>,
}

impl<'bump> Evaluatable<'bump> for BaseFunction<'bump> {
    fn get_evaluated(&self) -> Function<'bump> {
        self.eval_fun()
    }
}

impl<'a, 'bump> FixedSignature<'a, 'bump> for BaseFunction<'bump>
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

// impl<'a, 'bump> FixedSignature<'a, 'bump> for BaseFunction<'bump>
// where
//     'bump: 'a,
// {
//     fn as_fixed_signature(&'a self) -> FixedRefSignature<'a, 'bump> {
//         match self {
//             BaseFunction::Base(x) => x.as_fixed_signature(),
//             BaseFunction::Eval(e) => {
//                 let FixedRefSignature { out, args } = e.as_fixed_signature();
//                 let out = out.evaluated_sort().unwrap();
//                 let args: Option<VecRefClone<_>> =
//                     args.into_iter().map(|s| s.evaluated_sort()).collect();
//                 let args = args.unwrap();
//                 FixedRefSignature { out, args }
//             }
//         }
//     }
// }
