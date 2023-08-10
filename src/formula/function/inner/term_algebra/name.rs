use std::{ops::Deref, sync::Arc};

use hashbrown::HashMap;
use static_init::dynamic;

use crate::{
    formula::{
        formula::ARichFormula,
        function::{
            builtin::NAME_TO_MESSAGE,
            signature::FixedRefSignature,
            traits::{FixedSignature, MaybeEvaluatable},
            Function,
        },
        sort::{
            builtins::{MESSAGE, NAME},
            Sort,
        },
    },
    implvec,
    utils::{vecref::{VecRef, VecRefClone}, string_ref::StrRef},
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
pub struct Name<'bump> {
    name: String,
    target: Sort<'bump>,
    args: Arc<[Sort<'bump>]>,
}

impl<'bump> Name<'bump> {
    pub fn new(name: String, target: Sort<'bump>, args: implvec!(Sort<'bump>)) -> Self {
        Self {
            name,
            target,
            args: args.into_iter().collect(),
        }
    }

    pub fn args(&self) -> &[Sort<'bump>] {
        self.args.as_ref()
    }

    pub fn target(&self) -> Sort<'bump> {
        self.target
    }

    pub fn name(&self) -> &str {
        self.name.as_ref()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy)]
pub struct NameCaster<'bump> {
    target: Sort<'bump>,
}

impl<'bump> NameCaster<'bump> {
    pub fn new(target: Sort<'bump>) -> Self {
        Self { target }
    }

    pub fn target(&self) -> Sort<'bump> {
        self.target
    }

    pub fn name(&self) -> StrRef<'_> {
        format!("cast${}$name", self.target.name()).into()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NameCasterCollection<'bump> {
    content: HashMap<Sort<'bump>, Function<'bump>>,
}

impl<'bump> NameCasterCollection<'bump> {
    pub fn new(content: HashMap<Sort<'bump>, Function<'bump>>) -> Self {
        Self { content }
    }

    pub fn cast_function(&self, sort: &Sort<'bump>) -> Option<&Function<'bump>> {
        self.content.get(sort)
    }

    pub fn cast(
        &self,
        sort: Sort<'bump>,
        f: impl Into<ARichFormula<'bump>>,
    ) -> ARichFormula<'bump> {
        self.cast_function(&sort).unwrap().f_a([f])
    }

    pub fn content_mut(&mut self) -> &mut HashMap<Sort<'bump>, Function<'bump>> {
        &mut self.content
    }
}

impl<'bump> FromIterator<(Sort<'bump>, Function<'bump>)> for NameCasterCollection<'bump> {
    fn from_iter<T: IntoIterator<Item = (Sort<'bump>, Function<'bump>)>>(iter: T) -> Self {
        Self {
            content: iter.into_iter().collect(),
        }
    }
}

impl<'bump> MaybeEvaluatable<'bump> for Name<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}

impl<'bump> MaybeEvaluatable<'bump> for NameCaster<'bump> {
    fn maybe_get_evaluated(&self) -> Option<Function<'bump>> {
        None
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for Name<'bump> {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        let args = self.args().into();
        FixedRefSignature {
            out: NAME.clone(),
            args,
        }
    }
}

impl<'a, 'bump: 'a> FixedSignature<'a, 'bump> for NameCaster<'bump> {
    fn as_fixed_signature(
        &'a self,
    ) -> crate::formula::function::signature::FixedRefSignature<'a, 'bump> {
        FixedRefSignature {
            out: self.target(),
            args: VecRefClone::VecRef(VecRef::Single(Deref::deref(&NAME))),
        }
    }
}

#[dynamic]
pub static DEFAULT_NAME_CASTER: NameCasterCollection<'static> = NameCasterCollection {
    content: [(MESSAGE.as_sort(), NAME_TO_MESSAGE.clone())]
        .into_iter()
        .collect(),
};
