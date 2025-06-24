use crate::{input::Registerable, terms::Sort};
use cryptovampire_smt::{SortedVar, VarInner};
use itertools::izip;
use log::trace;
use serde::{Deserialize, Serialize};
use steel::{rvals::{FromSteelVal, IntoSteelVal}, steel_vm::register_fn::RegisterFn};
use steel_derive::Steel;
use utils::implvec;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Steel)]
pub struct Signature {
    pub inputs: cow![Sort],
    pub output: Sort,
}

impl Signature {
    pub fn new(inputs: implvec!(Sort), output: Sort) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            output,
        }
    }

    pub fn arity(&self) -> usize {
        self.inputs.len()
    }

    pub fn inputs_iter(&self) -> impl Iterator<Item = Sort> + use<'_> {
        self.inputs.iter().copied()
    }

    pub fn mk_sorted_vars(&self, from: u32) -> impl Iterator<Item = SortedVar<Sort>> + use<'_> {
        izip!(from.., self.inputs.iter()).map(|(i, s)| SortedVar {
            var: VarInner::Int(i),
            sort: *s,
        })
    }

    fn steel_constructor(input: Vec<Sort>, output: Sort) -> Self {
        Self { inputs: input.into(), output }
    }
}

impl Registerable for Signature {
    fn register(module: &mut steel::steel_vm::builtin::BuiltInModule) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module).register_fn("mk-signature", Self::steel_constructor)
    }
}