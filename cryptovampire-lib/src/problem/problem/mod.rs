// pub mod builder;
mod pbl_iterator;
use hashbrown::HashSet;
use log::trace;
pub use pbl_iterator::PblIterator;

use std::{
    cell::RefCell,
    collections::{BTreeMap, VecDeque},
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
        function::{
            inner::evaluate::Evaluator, name_caster_collection::NameCasterCollection, Function,
        },
        sort::{builtins::CONDITION, Sort},
        variable::Variable,
    },
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
    pub extra_instances: HashSet<ARichFormula<'bump>>
}

impl<'bump> Problem<'bump> {
    fn list_top_level_terms_no_extra<'a>(&'a self) -> impl Iterator<Item = &'a ARichFormula<'bump>>
    where
        'bump: 'a,
    {
        itertools::chain!(
            &self.assertions,
            [&self.query],
            &self.lemmas,
            self.protocol.list_top_level_terms_short_lifetime(),
            // &self.extra_instances
        )
    }
    pub fn list_top_level_terms<'a>(&'a self) -> impl Iterator<Item = &'a ARichFormula<'bump>>
    where
        'bump: 'a,
    {
        // itertools::chain!(
        //     self.list_top_level_terms_no_extra(),
        //     &self.extra_instances
        // )
        itertools::chain!(
            &self.assertions,
            [&self.query],
            &self.lemmas,
            self.protocol.list_top_level_terms_short_lifetime(),
            &self.extra_instances
        )
    }

    pub fn max_var(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.list_top_level_terms()
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| id)
            .max()
            .unwrap_or(0)
            + 1
    }

    /// [Self::max_var] without [Self::extra_instances]
    pub fn max_var_no_extras(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.list_top_level_terms_no_extra()
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| id)
            .max()
            .unwrap_or(0)
            + 1
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
        trace!("genrating problem file...");

        trace!("[G]\t- sort declarations...");
        declarations.extend(
            self.sorts
                .iter()
                .filter(|s| !(s.is_datatype(env) || s.is_solver_built_in() || s.is_evaluated()))
                .filter(|&&s| s != CONDITION.as_sort())
                .map(|s| Declaration::Sort(*s)),
        );

        {
            declarations.reserve(self.functions.len());
            // let mut datatypes = Vec::new();
            let mut datatypes = BTreeMap::new();
            for &fun in self.functions.iter().filter(|f| !f.is_builtin()) {
                // declare the function as datatypes if
                //  - it must always be a datatype
                //  - it's a symbolic term and we're in the symbolic realm
                if fun.is_always_datatype() || (fun.is_term_algebra() && env.is_symbolic_realm()) {
                    debug_assert_eq!(fun.fast_outsort().map(|s| s.is_datatype(env)), Some(true));
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
        trace!("[G]\t\t[DONE]");

        trace!("[G]\t- ordering...");
        order::generate(assertions, declarations, env, self);
        trace!("[G]\t\t[DONE]");

        trace!("[G]\t- evaluate...");
        general_assertions::evaluate::generate(assertions, declarations, env, self);
        trace!("[G]\t\t[DONE]");

        trace!("[G]\t- crypto...");
        assertions.push(Axiom::Comment("crypto".into()));
        for crypto in &self.crypto_assertions {
            trace!("{:?}", crypto);
            crypto.generate(assertions, declarations, env, self)
        }
        trace!("[G]\t\t[DONE]");

        // assertions.sort();

        trace!("[G]\t- user assertions...");
        assertions.push(Axiom::Comment("user asserts".into()));
        assertions.extend(
            self.assertions
                .iter()
                .cloned()
                .map(|a| propagate_evaluate(a.as_ref(), &self.evaluator))
                .map(Axiom::base),
        );
        trace!("[G]\t\t[DONE]");

        trace!("[G]\t- query...");
        assertions.push(Axiom::Comment("query".into()));
        assertions.push(Axiom::Query {
            formula: propagate_evaluate(self.query.as_ref(), &self.evaluator),
        });

        trace!("[G]\t\t[DONE]");
        trace!("generation done");

        declarations.sort();
    }
}
