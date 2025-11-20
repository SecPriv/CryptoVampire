use std::borrow::Cow;

use bon::bon;
use utils::implvec;

use self::function_builder::{
    SetAlias, SetCryptography, SetInputs, SetName, SetOutput, SetStepIdx,
};
use super::*;
use crate::terms::{
    Alias, Function, FunctionCollection, FunctionFlags, InnerFunction, Signature, Sort,
};
use crate::utils::fresh_name;

impl Problem {
    /// Returns the function collection
    pub fn functions(&self) -> &FunctionCollection {
        &self.function
    }

    /// Returns a mutable reference to the function collection
    pub fn functions_mut(&mut self) -> &mut FunctionCollection {
        self.clear_smt_prelude();
        &mut self.function
    }
}

#[bon]
impl Problem {
    /// Declares a new function
    ///
    /// This function returns a [FunctionBuilder] that can be used to build a new function.
    #[builder(builder_type = FunctionBuilder)]
    pub fn declare_function(
        &mut self,
        #[builder(field)] flags: FunctionFlags,
        #[builder(into)] name: Cow<'static, str>,
        #[builder(with = FromIterator::from_iter, default = vec![])] inputs: Vec<Sort>,
        output: Sort,
        alias: Option<Alias>,
        #[builder(default = 0)] quantifier_idx: usize,
        #[builder(default = 0)] protocol_idx: usize,
        #[builder(default = 0)] step_idx: usize,
        #[builder(with = FromIterator::from_iter, default = vec![])] cryptography: Vec<usize>,
    ) -> Function {
        let signature = Signature::new(inputs, output);
        let inner = InnerFunction {
            name,
            signature,
            alias,
            flags,
            quantifier_idx,
            protocol_idx,
            step_idx,
            cryptography: cryptography.into(),
        };
        let fun = Function::new(inner);
        self.functions_mut().add(fun.clone());
        fun
    }
}

use self::function_builder::IsUnset as FunctionBuilderIsUnset;
impl<'a, S> FunctionBuilder<'a, S>
where
    S: function_builder::State,
{
    /// Adds a flag to the function
    pub fn flag(mut self, flag: FunctionFlags) -> Self {
        self.flags |= flag;
        self
    }

    /// Adds multiple flags to the function
    pub fn flags(self, flags: implvec!(FunctionFlags)) -> Self {
        flags.into_iter().fold(self, |acc, flag| acc.flag(flag))
    }

    /// Sets the function as a step function
    pub fn step(self, idx: usize) -> FunctionBuilder<'a, SetOutput<SetStepIdx<SetAlias<S>>>>
    where
        S::StepIdx: FunctionBuilderIsUnset,
        S::Alias: FunctionBuilderIsUnset,
        S::Output: FunctionBuilderIsUnset,
    {
        self.maybe_alias(None)
            .step_idx(idx)
            .flag(FunctionFlags::STEP)
            .output(Sort::Time)
    }

    /// Try to assign `name` to [Self::name], but generate a fresh name if it's
    /// already taken
    pub fn fresh_name(self, name: impl AsRef<str>) -> FunctionBuilder<'a, SetName<S>>
    where
        S::Name: FunctionBuilderIsUnset,
    {
        let name = fresh_name(
            name.as_ref(),
            self.self_receiver.function.registered_names(),
        );
        self.name(name)
    }

    /// Allocates a new cryptographic assumption and assigns it to the function
    pub fn and_allocate_cyptographic_assumption(
        self,
        num: usize,
        start: Option<&mut usize>,
    ) -> FunctionBuilder<'a, SetCryptography<S>>
    where
        S::Cryptography: FunctionBuilderIsUnset,
    {
        let len = self.self_receiver.cryptography.len();
        self.self_receiver
            .cryptography
            .extend((0..num).map(|_| Default::default()));
        if let Some(start) = start {
            *start = len
        };
        self.cryptography(len..(len + num))
    }

    /// Sets the function as temporary
    pub fn temporary(self) -> Self {
        self.set_temporary(true)
    }

    /// Sets the function as temporary or not
    pub fn set_temporary(mut self, value: bool) -> Self {
        if value {
            self.flags |= FunctionFlags::TEMPORARY
        } else {
            self.flags -= FunctionFlags::TEMPORARY
        }
        self
    }

    /// Sets the signature of the function
    pub fn signature(
        self,
        Signature { inputs, output }: Signature,
    ) -> FunctionBuilder<'a, SetInputs<SetOutput<S>>>
    where
        S::Inputs: FunctionBuilderIsUnset,
        S::Output: FunctionBuilderIsUnset,
    {
        self.output(output).inputs(inputs.iter().copied())
    }
}
