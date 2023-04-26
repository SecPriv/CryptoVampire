use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    container::Container,
    environement::environement::Environement,
    formula::{
        file_descriptior::{
            axioms::Axiom,
            declare::{ConstructorDestructor, DataType, Declaration},
        },
        formula::RichFormula,
        function::{
            evaluate::Evaluator, term_algebra::name::NameCaster, Function,
        },
        sort::Sort,
        variable::Variable,
    },
};

use super::{
    crypto_assumptions::CryptoAssumption,
    general_assertions::{self, order},
    generator::Generator,
    protocol::Protocol,
};

#[derive(Debug, Clone)]
pub struct Problem<'bump> {
    container: &'bump Container<'bump>,
    /// functions to declare (not already declared somewhere else)
    pub functions: Vec<Function<'bump>>, // to keep track of 'static functions
    pub sorts: Vec<Sort<'bump>>, // same
    pub evaluator: Rc<Evaluator<'bump>>,
    pub name_caster: Rc<NameCaster<'bump>>,
    pub protocol: Protocol<'bump>,
    pub assertions: Vec<RichFormula<'bump>>,
    pub crypto_assertions: Vec<CryptoAssumption<'bump>>,
    pub query: Box<RichFormula<'bump>>,
}

impl<'bump> Problem<'bump> {
    pub fn list_top_level_terms<'a>(&'a self) -> impl Iterator<Item = &'a RichFormula<'bump>>
    where
        'bump: 'a,
    {
        self.assertions
            .iter()
            .chain(std::iter::once(self.query.as_ref()))
            .chain(self.protocol.list_top_level_terms_short_lifetime())
    }

    pub fn max_var(&self) -> usize {
        let pile = RefCell::new(Vec::new());

        self.list_top_level_terms()
            .flat_map(|f| f.used_variables_iter_with_pile(pile.borrow_mut()))
            .map(|Variable { id, .. }| *id)
            .max()
            .unwrap_or(0)
    }

    pub fn container(&self) -> &'bump Container<'bump> {
        self.container
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
                if fun.is_term_algebra() && !env.not_as_term_algebra() {
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
        assertions.extend(self.assertions.iter().cloned().map(Axiom::base));

        assertions.push(Axiom::Comment("query".into()));
        assertions.push(Axiom::Query {
            formula: self.query.clone(),
        })
    }
}
