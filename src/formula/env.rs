use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;

use super::{
    builtins::init::init_env,
    cli::Args,
    function::{FFlags, Function},
    sort::Sort,
};

#[derive(Debug, Clone)]
pub struct Environement {
    functions: HashMap<String, Function>,
    sorts: HashMap<String, Sort>,
    skolems: usize,
    args: Rc<Args>,
}

// #[derive(Debug, Clone)]
// pub struct InnerEnvironement {
//     use_rewrite: bool,
//     crypto_rewrite: bool,
//     use_special_subterm: bool,
//     assert_theory: bool,
// }

// impl Default for Environement {
//     fn default() -> Self {
//         let mut env = Self {
//             functions: HashMap::new(),
//             sorts: HashMap::new(),
//             inner: Box::new(InnerEnvironement {
//                 use_rewrite: false,
//                 crypto_rewrite: false,
//                 use_special_subterm: false,
//                 assert_theory: false,
//             }),
//         };
//         init_env(&mut env);
//         env
//     }
// }

impl Environement {
    pub fn empty(args: Rc<Args>) -> Self {
        let mut env = Environement {
            functions: HashMap::new(),
            sorts: HashMap::new(),
            skolems: 0,
            args,
        };
        init_env(&mut env, Self::get_sorts_mut);
        env
    }

    pub fn get_f<'a>(&'a self, s: &str) -> Option<&'a Function> {
        self.functions.get(s)
    }

    /// add a function to the environement
    ///
    /// return true if the functions was *not* in self,
    /// false otherwise
    ///
    /// Note that the functions isn't inserted if it was already in
    pub fn add_f(&mut self, f: Function) -> bool {
        // dbg!(f.name());
        let ptr = f.as_ptr_usize();
        self.functions
            .entry(f.name().to_owned())
            .or_insert(f)
            .as_ptr_usize()
            == ptr
    }

    pub fn add_skolem<'a>(
        &mut self,
        fv_sorts: impl Iterator<Item = &'a Sort>,
        sort: &Sort,
    ) -> Function {
        let name = format!("sk${}", self.skolems);
        self.skolems += 1;

        let function = Function::new_with_flag(
            &name,
            fv_sorts.cloned().collect(),
            sort.clone(),
            FFlags::SKOLEM,
        );
        assert!(self.add_f(function.clone()));
        function
    }

    pub fn get_s<'a>(&'a self, s: &str) -> Option<&'a Sort> {
        self.sorts.get(s)
    }

    pub fn add_s(&mut self, f: Sort) -> bool {
        let ptr = f.as_ptr_usize();
        self.sorts
            .entry(f.name().to_owned())
            .or_insert(f)
            .as_ptr_usize()
            == ptr
    }

    fn get_sorts_mut(&mut self) -> &mut HashMap<String, Sort> {
        &mut self.sorts
    }

    pub fn use_special_subterm(&self) -> bool {
        self.args.vampire_subterm
    }

    pub fn crypto_rewrite(&self) -> bool {
        self.args.crypto_rewrite
    }

    pub fn use_rewrite(&self) -> bool {
        self.args.eval_rewrite
    }

    pub fn use_assert_theory(&self) -> bool {
        self.args.assert_theory
    }

    pub fn skolemnise(&self) -> bool {
        self.args.skolemnise
    }

    // pub fn preprocessed_input(&self) -> bool {
    //     self.args.input_subterm_preprocessed
    // }

    pub fn preprocessing_plus(&self) -> bool {
        self.args.preprocessing
    }

    pub fn legacy_evaluate(&self) -> bool {
        self.args.legacy_evaluate
    }

    pub fn no_bitstring_fun(&self) -> bool {
        self.args.no_bitstring_fun
    }

    pub fn cvc5(&self) -> bool {
        self.args.cvc5
    }

    pub fn no_ta(&self) -> bool {
        self.args.no_term_algebra
    }

    // pub fn get_functions(&self) -> &HashMap<String, Function> {
    //     &self.functions
    // }

    pub fn get_functions_mut(&mut self) -> &mut HashMap<String, Function> {
        &mut self.functions
    }

    pub fn extend_functions(&mut self, iter: impl Iterator<Item = Function>) {
        self.functions
            .extend(iter.map(|f| (f.name().to_owned(), f)))
    }

    pub fn get_functions_iter(&self) -> impl Iterator<Item = &Function> {
        self.functions.values()
    }

    pub fn get_functions_iter_mut(&mut self) -> impl Iterator<Item = &mut Function> {
        self.functions.values_mut()
    }

    // pub fn get_sorts(&self) -> &HashMap<String, Sort> {
    //     &self.sorts
    // }

    // pub fn get_sorts_mut(&mut self) -> &mut HashMap<String, Sort> {
    //     &mut self.sorts
    // }

    pub fn get_sort_iter(&self) -> impl Iterator<Item = &Sort> {
        self.sorts.values().unique()
    }

    pub fn get_sort_iter_mut(&mut self) -> impl Iterator<Item = &mut Sort> {
        self.sorts.values_mut()
    }

    pub fn extend_sorts(&mut self, iter: impl Iterator<Item = Sort>) {
        self.sorts.extend(iter.map(|s| (s.name().to_owned(), s)))
    }

    pub fn create_and_add_function(
        &mut self,
        name: &str,
        inputs: &[&Sort],
        output: &Sort,
        flags: FFlags,
    ) -> Function {
        let f = Function::new_with_flag(
            name,
            inputs.iter().map(|&s| s.clone()).collect(),
            output.clone(),
            flags,
        );
        let old_f = self.functions.entry(name.to_owned()).or_insert(f.clone());
        if f.hard_eq(old_f) {
            old_f.clone()
        } else {
            panic!(
                "a different function named \"{}\" already exists ({:?})",
                f.name(),
                old_f
            )
        }
    }

    pub fn get_or_create<'a>(
        &'a mut self,
        name: &str,
        inputs: &[&Sort],
        output: &Sort,
        flags: FFlags,
    ) -> &'a Function {
        self.functions
            .entry(name.to_owned())
            .or_insert(Function::new_with_flag(
                name,
                inputs.iter().map(|&s| s.clone()).collect(),
                output.clone(),
                flags,
            ))
    }

    pub fn verify_f(&self) -> bool {
        self.functions.iter().all(|(name, f)| name == f.name())
    }

    pub fn verify_s(&self) -> bool {
        self.sorts.iter().all(|(name, f)| name == f.name())
    }

    pub fn contains_f(&self, f: &Function) -> bool {
        self.get_f(f.name()) == Some(f)
    }

    pub fn contains_s(&self, f: &Sort) -> bool {
        self.get_s(f.name()) == Some(f)
    }

    pub fn contain_key_f(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }

    pub fn len_fun(&self) -> usize {
        self.functions.len()
    }

    pub fn len_sort(&self) -> usize {
        self.sorts.len()
    }
}
