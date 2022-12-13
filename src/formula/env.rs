use std::collections::HashMap;

use super::{function::Function, sort::Sort};

pub struct Environement<'a> {
    functions: &'a mut HashMap<String, Function>,
    naming_min_size: usize,
    naming_current: usize,
    skolem_current: usize,
}

impl<'a> Environement<'a> {
    fn naming_min_size(&self) -> usize {
        self.naming_min_size
    }

    fn is_name_free(&self, name: &str) -> bool {
        self.functions.contains_key(&name.to_owned())
    }

    /// if it returns something, you messed up
    fn add_function(&mut self, f: Function) -> Option<Function> {
        self.functions.insert(f.name().to_owned(), f)
    }

    pub fn new_skolem(
        &mut self,
        free_vars_sorts: impl Iterator<Item = Sort>,
        sort: Sort,
    ) -> Function {
        let f = Function::new_skolem(self.skolem_current, free_vars_sorts.collect(), sort);

        assert!(self.is_name_free(f.name()));

        self.skolem_current += 1;
        self.add_function(f.clone());
        f
    }
}
