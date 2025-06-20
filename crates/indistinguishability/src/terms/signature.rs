use crate::{input::Registerable, terms::Sort};
use cryptovampire_smt::{SortedVar, VarInner};
use itertools::izip;
use serde::{Deserialize, Serialize};
use steel::rvals::{FromSteelVal, IntoSteelVal};
use utils::implvec;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
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
}

impl FromSteelVal for Signature {
    fn from_steelval(val: &steel::SteelVal) -> steel::rvals::Result<Self> {
        let (args, out): (Vec<Sort>, Sort) = FromSteelVal::from_steelval(val)?;
        Ok(Self {
            inputs: args.into(),
            output: out,
        })
    }
}

impl IntoSteelVal for Signature {
    fn into_steelval(self) -> steel::rvals::Result<steel::SteelVal> {
        let Self { inputs, output } = self;
        (inputs.into_owned(), output).into_steelval()
    }
}
