use std::borrow::Cow;
use std::collections::HashMap;

use itertools::chain;
use log::trace;

use super::{BUILTINS, Function, PARSING_PAIRS};
use crate::terms::Quantifier;

/// see [Self::valid] for the invariants
#[derive(Debug, Default)]
pub struct FunctionCollection {
    functions: Vec<Function>,
    map_function: HashMap<Cow<'static, str>, Function>,
    quantifiers: Vec<Quantifier>,

    temporary_functions: Vec<Function>,
    temporary_quantifiers: Vec<Quantifier>,
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
        true
    }

    pub fn get(&self, name: &str) -> Option<Function> {
        self.map_function.get(name).cloned()
    }

    /// iterate over temporary and non temporary functions
    pub fn iter_current(&self) -> impl Iterator<Item = &Function> {
        chain![&self.functions, &self.temporary_functions]
    }

    /// iterate over the constant quantifiers and the temporary ones
    pub fn current_quantifiers(&self) -> impl Iterator<Item = &Quantifier> {
        chain![&self.quantifiers, &self.temporary_quantifiers]
    }

    pub fn quantifiers(&self, temporary: bool) -> &[Quantifier] {
        if temporary {
            &self.temporary_quantifiers
        } else {
            &self.quantifiers
        }
    }

    fn quantifiers_mut(&mut self, temporary: bool) -> &mut Vec<Quantifier> {
        if temporary {
            &mut self.temporary_quantifiers
        } else {
            &mut self.quantifiers
        }
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
        if fun.is_temporary() {
            self.temporary_functions.push(fun);
        } else {
            self.functions.push(fun);
        }
    }

    pub(crate) fn push_quantifier(&mut self, q: Quantifier) -> &mut Quantifier {
        let quantifiers = self.quantifiers_mut(q.temporary());
        quantifiers.push(q);
        quantifiers.last_mut().unwrap()
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

    pub fn clear_temporary(&mut self) {
        let Self {
            map_function,
            temporary_functions,
            temporary_quantifiers,
            ..
        } = self;

        map_function.retain(|_, f| temporary_functions.contains(f));

        temporary_functions.clear();
        temporary_quantifiers.clear();
        assert!(self.valid());
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuantifierIndex {
    pub temporary: bool,
    pub index: usize,
}

pub static TEMPORARY: QuantifierIndex = QuantifierIndex {
    temporary: true,
    index: 0,
};
pub static CONSTANT: QuantifierIndex = QuantifierIndex {
    temporary: false,
    index: 0,
};

impl QuantifierIndex {
    pub fn get(self, functions: &FunctionCollection) -> Option<&Quantifier> {
        functions.quantifiers(self.temporary).get(self.index)
    }

    pub fn get_mut(self, functions: &mut FunctionCollection) -> Option<&mut Quantifier> {
        functions
            .quantifiers_mut(self.temporary)
            .get_mut(self.index)
    }

    pub fn get_array(self, functions: &FunctionCollection) -> &[Quantifier] {
        functions.quantifiers(self.temporary)
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
