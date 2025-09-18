use std::borrow::Cow;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;
use std::sync::atomic::AtomicUsize;

use egg::Var;
use itertools::{Itertools, chain};
use log::trace;
use utils::implvec;

use super::{BUILTINS, Exists, Function, FunctionFlags, PARSING_PAIRS};
use crate::terms::{InnerFunction, Quantifier, Signature, Sort};

/// The numbe of declared existential quantifiers
///
/// This is used to generate unique names
// pub(crate) static QUANTIFIER_COUNT: AtomicUsize = AtomicUsize::new(0);

/// see [Self::valid] for the invariants
#[derive(Debug, Default)]
pub struct FunctionCollection {
    functions: Vec<Function>,
    temporary_functions: Vec<Function>,
    map_function: HashMap<Cow<'static, str>, Function>,
    quantifiers: Vec<Quantifier>,
}

impl FunctionCollection {
    pub fn init() -> Self {
        let functions = BUILTINS.to_vec();
        let map_function = PARSING_PAIRS
            .iter()
            .map(|(n, f)| (Cow::from(*n), f.clone()))
            .collect();
        Self {
            functions,
            map_function,
            ..Default::default()
        }
    }

    /// Checks that the stuct follows its invariants
    ///
    /// That is: there are no duplicates in `functions` and `map_function` only
    /// contains function in `functions` and it contains them all
    pub fn valid(&self) -> bool {
        // TODO
        true
    }

    pub fn get(&self, name: &str) -> Option<Function> {
        self.map_function.get(name).cloned()
    }

    pub fn quantifiers(&self) -> &[Quantifier] {
        &self.quantifiers
    }

    /// Lists all the registered nonces
    pub fn nonces(&self) -> impl Iterator<Item = &Function> {
        self.functions.iter().filter(|f| f.is_nonce())
    }

    /// Lists all the registered protocols
    pub fn protocols(&self) -> impl Iterator<Item = &Function> {
        self.functions.iter().filter(|f| f.is_protocol())
    }

    /// add a [Function] to the collection
    ///
    /// ### panics
    /// If a [Function] with the same name is already registered
    pub fn add(&mut self, fun: Function) {
        trace!("adding {fun:?}");
        let r = self.map_function.insert(fun.name.clone(), fun.clone());
        assert!(
            r.is_none(),
            "the function '{}' was already in the database",
            fun.name
        );
        self.functions.push(fun);
    }

    pub fn get_mut_quantifier(&mut self, index: usize) -> Option<&mut Quantifier> {
        self.quantifiers.get_mut(index)
    }

    pub(crate) fn push_quantifier(&mut self, q: Quantifier) -> &mut Quantifier {
        self.quantifiers.push(q);
        self.quantifiers.last_mut().unwrap()
    }

    /// Add a name alias for a function
    ///
    /// This doesn't check wether the function is part of the main array
    ///
    /// ### panics
    /// If the name is already taken
    pub fn add_other_name(&mut self, fun: Function, name: Cow<'static, str>) {
        let r = self.map_function.insert(name, fun);
        assert!(r.is_none(), "the function was already in the database");
    }

    pub fn registered_names(&self) -> impl Iterator<Item = &str> {
        self.map_function.keys().map(|f| f.as_ref())
    }
}

#[macro_export]
macro_rules! decl_fun{
    ($pbl:expr; $name:literal : ($($s:expr),*) -> Nonce ) => {
        {
            use $crate::terms::Sort::*;
            // let collection = ::std::convert::AsMut::<$crate::terms::FunctionCollection>::as_mut($pbl);
            $pbl.declare_function()
                .name($name)
                .inputs([$($s),*])
                .output(Nonce)
                .flags($crate::terms::flags::FunctionFlags::NONCE)
                .call()
        }
    };
    ($pbl:expr; $name:literal : ($($s:expr),*) -> $o:expr ) => {
        {
            use $crate::terms::Sort::*;
            // let collection = ::std::convert::AsMut::<$crate::terms::FunctionCollection>::as_mut($pbl);
            $pbl.declare_function()
                .name($name)
                .inputs([$($s),*])
                .output($o)
                .call()
        }
    }
}

impl Deref for FunctionCollection {
    type Target = [Function];

    fn deref(&self) -> &Self::Target {
        &self.functions
    }
}

#[cfg(test)]
mod test {
    use crate::terms::FunctionCollection;

    /// [FunctionCollection::init] produces a valid collection
    #[test]
    fn init_valid() {
        assert!(FunctionCollection::init().valid())
    }
}
