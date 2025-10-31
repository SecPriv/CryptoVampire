// pub mod builder;
mod pbl_iterator;
use std::collections::{BTreeMap, VecDeque};
use std::sync::Arc;

use derive_builder::Builder;
use hashbrown::HashSet;
use log::trace;
use logic_formula::iterators::UsedVariableIterator;
pub use pbl_iterator::PblIterator;
use utils::implvec;

use super::crypto_assumptions::CryptoAssumption;
use super::general_assertions::assertion_preprocessor::propagate_evaluate;
use super::general_assertions::{self, order};
use super::generator::Generator;
use super::protocol::Protocol;
use crate::container::ScopedContainer;
use crate::environement::environement::Environement;
use crate::error::BaseError;
use crate::formula::file_descriptior::GeneralFile;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::{ConstructorDestructor, DataType, Declaration};
use crate::formula::formula::ARichFormula;
use crate::formula::function::Function;
use crate::formula::function::inner::evaluate::Evaluator;
use crate::formula::function::name_caster_collection::NameCasterCollection;
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::CONDITION;
use crate::formula::variable::{IntoVariableIter, uvar};

#[derive(Debug, Clone, Builder)]
pub struct Problem<'bump> {
    container: &'bump ScopedContainer<'bump>,
    /// [Function]s to declare (not already declared somewhere else)
    functions: Vec<Function<'bump>>, // to keep track of 'static functions
    /// [Sort]s to declare (not already declared somewhere else)
    sorts: Vec<Sort<'bump>>, // same
    evaluator: Arc<Evaluator<'bump>>,
    name_caster: Arc<NameCasterCollection<'bump>>,
    protocol: Protocol<'bump>,
    #[builder(default)]
    assertions: Vec<ARichFormula<'bump>>,
    #[builder(default)]
    crypto_assertions: Vec<CryptoAssumption<'bump>>,
    #[builder(default)]
    lemmas: VecDeque<ARichFormula<'bump>>,
    #[builder(setter(into))]
    query: ARichFormula<'bump>,
    #[builder(default)]
    extra_instances: HashSet<ARichFormula<'bump>>,
}

impl From<ProblemBuilderError> for BaseError {
    fn from(val: ProblemBuilderError) -> Self {
        BaseError::BuilderError(Box::new(val))
    }
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

    pub fn max_var(&self) -> uvar {
        UsedVariableIterator::with(self.list_top_level_terms()).max_var()
    }

    /// [Self::max_var] without [Self::extra_instances]
    pub fn max_var_no_extras(&self) -> uvar {
        UsedVariableIterator::with(self.list_top_level_terms_no_extra()).max_var()
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

    /// return the number of new instances added
    pub fn extend_extra_instances(&mut self, instances: implvec!(ARichFormula<'bump>)) -> usize {
        let pre = self.extra_instances.len();
        self.extra_instances.extend(instances);
        let n = self.extra_instances.len() - pre;
        trace!("added {n} instances");
        n
    }

    pub fn functions(&self) -> &[Function<'bump>] {
        &self.functions
    }

    pub fn sorts(&self) -> &[Sort<'bump>] {
        &self.sorts
    }

    pub fn evaluator(&self) -> &Evaluator<'bump> {
        &self.evaluator
    }

    pub fn name_caster(&self) -> &NameCasterCollection<'bump> {
        &self.name_caster
    }

    pub fn owned_name_caster(&self) -> Arc<NameCasterCollection<'bump>> {
        Arc::clone(&self.name_caster)
    }

    pub fn protocol(&self) -> &Protocol<'bump> {
        &self.protocol
    }

    pub fn assertions(&self) -> &[ARichFormula<'bump>] {
        &self.assertions
    }

    pub fn crypto_assertions(&self) -> &[CryptoAssumption<'bump>] {
        &self.crypto_assertions
    }

    pub fn lemmas(&self) -> &VecDeque<ARichFormula<'bump>> {
        &self.lemmas
    }

    pub fn query(&self) -> &ARichFormula<'bump> {
        &self.query
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
