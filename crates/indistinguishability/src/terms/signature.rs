use serde::{Deserialize, Serialize};
use steel_derive::Steel;
use utils::implvec;

use crate::fresh;
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
}

mod msteel {
    use log::trace;
    use steel::steel_vm::builtin::BuiltInModule;

    use crate::input::Registerable;
    use crate::terms::{Signature, Sort};

    #[steel_derive::declare_steel_function(name = "new")]
    fn new(input: Vec<Sort>, output: Sort) -> Signature {
        Signature {
            inputs: input.into(),
            output,
        }
    }

    #[steel_derive::declare_steel_function(name = "inputs")]
    fn inputs(s: Signature) -> Vec<Sort> {
        s.inputs.to_vec()
    }

    #[steel_derive::declare_steel_function(name = "output")]
    fn output(s: Signature) -> Sort {
        s.output
    }

    impl Registerable for Signature {
        fn register(modules: &mut rustc_hash::FxHashMap<String, BuiltInModule>) {
            let name = "cryptovampire/ll/signature";
            let mut module = BuiltInModule::new(name);
            module
                .register_type::<Signature>("Signature?")
                .register_native_fn_definition(NEW_DEFINITION)
                .register_native_fn_definition(INPUTS_DEFINITION)
                .register_native_fn_definition(OUTPUT_DEFINITION);
            trace!("defined {name} scheme module");
            assert!(modules.insert(name.into(), module).is_none());
        }
    }
}
