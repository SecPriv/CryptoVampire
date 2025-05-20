use std::{borrow::Cow, collections::HashMap, ops::Deref};

use itertools::Itertools;

use super::{Function, Quantifier, BUILTINS, PARSING_PAIRS};

/// see [Self::valid] for the invariants
#[derive(Debug, Default)]
pub struct FunctionCollection {
    functions: Vec<Function>,
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
        let Self {
            functions,
            map_function,
            quantifiers,
            ..
        } = self;

        // uniqueness
        let unique = functions.iter().all_unique();

        // relation between `functions` and `map_function`
        let mapping = crate::utils::same_slice(functions, map_function.values());

        // relation between `functions` and `quantifiers`
        let quantifiers_valid = quantifiers
            .iter()
            .enumerate()
            .all(|(idx, q)| q.valid(idx, self));
        let two_way_mapping = functions
            .iter()
            .enumerate()
            .filter_map(|(i, f)| f.get_exist_index().map(|idx| (i, idx)))
            .all(|(i, idx)| quantifiers[idx].points_to().contains(&i));

        unique && mapping && quantifiers_valid && two_way_mapping
    }

    pub fn get(&self, name: &str) -> Option<Function> {
        self.map_function.get(name).cloned()
    }

    pub fn quantifiers(&self) -> &[Quantifier] {
        &self.quantifiers
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
