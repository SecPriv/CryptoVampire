use serde::{Deserialize, Serialize};
use steel::steel_vm::register_fn::RegisterFn;
use steel_derive::Steel;
use utils::implvec;

use crate::fresh;
use crate::input::Registerable;
use crate::terms::{Formula, Sort, Variable};

/// Represents the signature of a function, defining its input and output sorts.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize, Steel)]
pub struct Signature {
    pub inputs: cow![Sort],
    pub output: Sort,
}

impl Signature {
    /// Creates a new `Signature` with the given input sorts and output sort.
    pub fn new(inputs: implvec!(Sort), output: Sort) -> Self {
        Self {
            inputs: inputs.into_iter().collect(),
            output,
        }
    }

    /// Returns the number of input arguments (arity) of the function.
    pub const fn arity(&self) -> usize {
        match &self.inputs {
            std::borrow::Cow::Borrowed(x) => x.len(),
            std::borrow::Cow::Owned(x) => x.len(),
        }
    }

    /// Returns an iterator over the input sorts of the function.
    pub fn inputs_iter(&self) -> impl Iterator<Item = Sort> + use<'_> {
        self.inputs.iter().copied()
    }

    /// Creates a vector of fresh `Variable`s, one for each input sort.
    pub fn mk_vars(&self) -> Vec<Variable> {
        self.inputs.iter().map(|&s| fresh!(s)).collect()
    }

    /// Creates a vector of fresh `Variable`s, one for each input sort.
    pub fn mk_vars_expr(&self) -> impl Iterator<Item = Formula> {
        self.inputs.iter().map(|&s| fresh!(s)).map(Formula::Var)
    }

    // pub fn mk_sorted_vars(
    //     &self,
    //     from: u32,
    // ) -> impl Iterator<Item = SortedVar<Sort>> + Clone + use<'_> {
    //     izip!(from.., self.inputs.iter()).map(|(i, s)| SortedVar {
    //         var: VarInner::Int(i as cryptovampire_smt::uvar),
    //         sort: *s,
    //     })
    // }

    // pub fn mk_egg_vars(&self, from: u32) -> impl Iterator<Item = egg::Var> {
    //     let n = self.arity() as u32 + from;
    //     (from..n).map(egg::Var::from_usize)
    // }

    fn steel_constructor(input: Vec<Sort>, output: Sort) -> Self {
        Self {
            inputs: input.into(),
            output,
        }
    }
}

impl Registerable for Signature {
    /// Registers the `Signature` type and its constructor with the Steel VM.
    fn register(
        module: &mut steel::steel_vm::builtin::BuiltInModule,
    ) -> &mut steel::steel_vm::builtin::BuiltInModule {
        Self::register_type(module).register_fn("mk-signature", Self::steel_constructor)
    }
}
