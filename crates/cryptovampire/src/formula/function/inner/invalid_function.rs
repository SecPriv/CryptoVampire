use super::super::signature::FixedRefSignature;
use super::super::traits::{MaybeEvaluatable, MaybeFixedSignature};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Default)]
pub struct InvalidFunction {
    // pub name: Option<StrRef<'bump>>,
    // pub args: Option<Vec<Sort<'bump>>>,
    // pub sort: Option<Sort<'bump>>,
}

impl InvalidFunction {
    // pub fn name(&self) -> Option<&str> {
    //     // self.name.as_ref().map(AsRef::as_ref)
    //     None
    // }

    // pub fn args(&self) -> Option<&[Sort<'bump>]> {
    //     // self.args.as_ref().map(Vec::as_slice)
    //     None
    // }

    // pub fn sort(&self) -> Option<Sort<'bump>> {
    //     // self.sort
    //     None
    // }
}

impl<'a, 'bump: 'a> MaybeFixedSignature<'a, 'bump> for InvalidFunction {
    fn maybe_fixed_signature(&'a self) -> Option<FixedRefSignature<'a, 'bump>> {
        // let out = self.sort()?;
        // let args = self.args()?.into();

        // Some(FixedRefSignature { out, args })
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for InvalidFunction {
    fn maybe_get_evaluated(&self) -> Option<super::super::Function<'bump>> {
        None
    }
}
