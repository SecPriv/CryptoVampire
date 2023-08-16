// pub mod builder;
mod pbl_iterator;
pub use pbl_iterator::PblIterator;

use std::{
    cell::RefCell,
    collections::{HashMap, VecDeque},
    sync::Arc,
};

use crate::{
    container::ScopedContainer,
    environement::environement::Environement,
    formula::{
        file_descriptior::{
            axioms::Axiom,
            declare::{ConstructorDestructor, DataType, Declaration},
            GeneralFile,
        },
        formula::ARichFormula,
        function::inner::{evaluate::Evaluator, term_algebra::name::NameCasterCollection},
        function::Function,
        sort::Sort,
        variable::Variable,
    },
    implvec, parser, utils::traits::NicerError,
};

use super::{
    crypto_assumptions::CryptoAssumption,
    general_assertions::{self, assertion_preprocessor::propagate_evaluate, order},
    generator::Generator,
    protocol::Protocol,
};

#[derive(Debug, Clone)]
pub struct Problem<'bump> {
    pub container: &'bump ScopedContainer<'bump>,
    /// functions to declare (not already declared somewhere else)
    pub functions: Vec<Function<'bump>>, // to keep track of 'static functions
    pub sorts: Vec<Sort<'bump>>, // same
    pub evaluator: Arc<Evaluator<'bump>>,
    pub name_caster: Arc<NameCasterCollection<'bump>>,
    pub protocol: Protocol<'bump>,
    pub assertions: Vec<ARichFormula<'bump>>,
    pub crypto_assertions: Vec<CryptoAssumption<'bump>>,
    pub lemmas: VecDeque<ARichFormula<'bump>>,
    pub query: ARichFormula<'bump>,
}

impl<'bump> Problem<'bump> {
    pub fn try_from_str<'a>(
        container: &'bump ScopedContainer<'bump>,
        sort_hash: implvec!(Sort<'bump>),
        function_hash: implvec!(Function<'bump>),
        extra_names: implvec!(String),
        str: &'a str,
    ) -> Result<Self, parser::E> {
        parser::parse_str(container, sort_hash, function_hash, extra_names, str).debug_continue()
    }

    pub fn list_top_level_terms<'a>(&'a self) -> impl Iterator<Item = &'a ARichFormula<'bump>>
    where
        'bump: 'a,
    {
        self.assertions
            .iter()
            .chain(std::iter::once(&self.query))
            .chain(self.protocol.list_top_level_terms_short_lifetime())
    }

    pub fn max_var(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.list_top_level_terms()
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| id)
            .max()
            .unwrap_or(0)
    }

    pub fn container(&self) -> &'bump ScopedContainer<'bump> {
        self.container
    }

    pub fn into_general_file(&self, env: &Environement<'bump>) -> GeneralFile<'bump> {
        let mut assertions = Vec::new();
        let mut declarations = Vec::new();
        self.generate(&mut assertions, &mut declarations, env, self);

        GeneralFile {
            assertions,
            declarations,
        }
    }
}

impl<'bump> Generator<'bump> for Problem<'bump> {
    fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        _: &Problem<'bump>,
    ) {
        declarations.extend(self.sorts.iter().map(|s| Declaration::Sort(*s)));

        {
            declarations.reserve(self.functions.len());
            // let mut datatypes = Vec::new();
            let mut datatypes = HashMap::new();
            for &fun in &self.functions {
                // declare the function as datatypes if
                //  - it must always be a datatype
                //  - it's a symbolic term and we're in the symbolic realm
                if fun.is_datatype() || (fun.is_term_algebra() && env.is_symbolic_realm()) {
                    let constr: &mut Vec<_> =
                        datatypes.entry(fun.fast_outsort().unwrap()).or_default();
                    constr.push(ConstructorDestructor::new_unused(self.container, fun))
                } else {
                    declarations.push(Declaration::FreeFunction(fun))
                }
            }

            declarations.push(Declaration::DataTypes(
                datatypes
                    .into_iter()
                    .map(|(sort, constructor_destructors)| DataType {
                        sort,
                        constructor_destructors,
                    })
                    .collect(),
            ));
        }

        order::generate(assertions, declarations, env, self);

        general_assertions::evaluate::generate(assertions, declarations, env, self);

        assertions.push(Axiom::Comment("crypto".into()));
        for crypto in &self.crypto_assertions {
            crypto.generate(assertions, declarations, env, self)
        }

        assertions.push(Axiom::Comment("user asserts".into()));
        assertions.extend(
            self.assertions
                .iter()
                .cloned()
                .map(|a| propagate_evaluate(a.as_ref(), &self.evaluator))
                .map(Axiom::base),
        );

        assertions.push(Axiom::Comment("query".into()));
        assertions.push(Axiom::Query {
            formula: propagate_evaluate(self.query.as_ref(), &self.evaluator),
        })
    }
}
