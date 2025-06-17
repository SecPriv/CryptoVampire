use super::{BUILTINS, Exists, Function, FunctionFlags, PARSING_PAIRS};
use crate::terms::{Alias, InnerFunction, Signature, Sort};
use bon::bon;
use egg::Var;
use itertools::{Itertools, chain};
use std::{borrow::Cow, collections::HashMap, ops::Deref, sync::atomic::AtomicUsize};
use utils::implvec;

/// The numbe of declared existential quantifiers
///
/// This is used to generate unique names
static EXISTS_COUNT: AtomicUsize = AtomicUsize::new(0);

/// see [Self::valid] for the invariants
#[derive(Debug, Default)]
pub struct FunctionCollection {
    functions: Vec<Function>,
    map_function: HashMap<Cow<'static, str>, Function>,
    quantifiers: Vec<Exists>,
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
        let Self {
            functions,
            map_function,
            quantifiers,
            ..
        } = self;

        // uniqueness
        let unique = functions.iter().map(|f| &f.name).all_unique();

        // relation between `functions` and `map_function`
        let mapping = crate::utils::same_slice(functions, map_function.values());

        // relation between `functions` and `quantifiers`
        let quantifiers_valid = quantifiers
            .iter()
            .enumerate()
            .all(|(idx, q)| q.valid(idx, self));
        let two_way_mapping = functions
            .iter()
            .filter_map(|f| f.get_exist_index().map(|idx| (f, idx)))
            .all(|(f, idx)| quantifiers[idx].get_functions().contains(&f));

        dbg!(unique);
        dbg!(mapping);
        dbg!(quantifiers_valid);
        dbg!(two_way_mapping);

        unique && mapping && quantifiers_valid && two_way_mapping
    }

    pub fn get(&self, name: &str) -> Option<Function> {
        self.map_function.get(name).cloned()
    }

    pub fn quantifiers(&self) -> &[Exists] {
        &self.quantifiers
    }

    /// Lists all the registered nonces
    pub fn nonces(&self) -> impl Iterator<Item = &Function> {
        self.functions
            .iter()
            .filter(|f| f.flags.contains(FunctionFlags::NONCE))
    }

    /// add a [Function] to the collection
    ///
    /// ### panics
    /// If a [Function] with the same name is already registered
    pub fn add(&mut self, fun: Function) {
        let r = self.map_function.insert(fun.name.clone(), fun.clone());
        assert!(
            r.is_none(),
            "the function '{}' was already in the database",
            fun.name
        );
        self.functions.push(fun);
    }

    /// The returned [Exists] has it's [Exists::vars], [Exists::bound_var] and
    /// [Exists::patt] left empty.
    pub fn add_exists_function(
        &mut self,
        vars_sorts: implvec!(Sort),
        bound_var_sort: Sort,
    ) -> &mut Exists {
        // set up
        let vsorts = vars_sorts.into_iter().collect_vec();
        let bsort = bound_var_sort;

        let exists_idx = self.quantifiers.len();

        let n_exists = EXISTS_COUNT.fetch_add(1, std::sync::atomic::Ordering::AcqRel);

        // build the Functions
        let tlf;
        let skolem;
        let fresh;

        {
            // tlf
            let inner_tlf = {
                let name = format!("_exists${n_exists:}").into();
                let inputs = chain!(vsorts.iter().copied(), [bsort]);
                let signature = Signature::new(inputs, Sort::Bool);
                InnerFunction {
                    flags: FunctionFlags::EXISTS,
                    exists_idx,
                    ..InnerFunction::new(name, signature)
                }
            };
            tlf = Function::new(inner_tlf);
            self.add(tlf.clone());
        }

        {
            // skolem
            let inner_skolem = {
                let name = format!("_sk${n_exists:}").into();
                let inputs = vsorts;
                let signature = Signature::new(inputs, bsort);
                InnerFunction {
                    flags: FunctionFlags::SKOLEM,
                    exists_idx,
                    ..InnerFunction::new(name, signature)
                }
            };
            skolem = Function::new(inner_skolem);
            self.add(skolem.clone());
        }

        {
            // fresh
            let inner_fresh = {
                let name = format!("_exists_fresh${n_exists:}").into();
                let signature = Signature::new([], bsort);
                InnerFunction {
                    flags: FunctionFlags::EXISTS_FRESH,
                    exists_idx,
                    ..InnerFunction::new(name, signature)
                }
            };
            fresh = Function::new(inner_fresh);
            self.add(fresh.clone());
        }

        // declare the quantifier
        self.quantifiers.push(Exists {
            vars: vec![],
            bound_var: Var::from_u32(0),
            patt: std::iter::empty().collect(),
            tlf,
            skolem,
            fresh,
        });

        // return
        &mut self.quantifiers[exists_idx]
    }

    pub fn get_mut_quantifier(&mut self, idx: usize) -> &mut Exists {
        &mut self.quantifiers[idx]
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
}

#[bon]
impl FunctionCollection {
    #[builder]
    pub fn add_function(
        &mut self,
        #[builder(into)] name: Cow<'static, str>,
        #[builder(with = FromIterator::from_iter, default = vec![])] inputs: Vec<Sort>,
        output: Sort,
        alias: Option<Alias>,
        #[builder(default = FunctionFlags::empty())] flags: FunctionFlags,
        #[builder(default = 0)] exists_idx: usize,
        #[builder(default = 0)] protocol_idx: usize,
        #[builder(default = 0)] step_idx: usize,
    ) -> Function {
        let signature = Signature::new(inputs, output);
        let inner = InnerFunction {
            name,
            signature,
            alias,
            flags,
            exists_idx,
            protocol_idx,
            step_idx,
        };
        let fun = Function::new(inner);
        self.add(fun.clone());
        fun
    }
}

#[macro_export]
macro_rules! decl_fun{
    ($pbl:expr; $name:literal : ($($s:expr),*) -> Nonce ) => {
        {
            use $crate::terms::Sort::*;
            let collection = ::std::convert::AsMut::<$crate::terms::FunctionCollection>::as_mut($pbl);
            collection.add_function()
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
            let collection = ::std::convert::AsMut::<$crate::terms::FunctionCollection>::as_mut($pbl);
            collection.add_function()
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
