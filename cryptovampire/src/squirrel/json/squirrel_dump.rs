use std::hash::Hash;

use hashbrown::HashMap;
use serde::{Deserialize, Serialize};
use utils::implvec;

use super::*;

#[derive(Serialize, Deserialize, Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
pub struct SquirrelDump<'a> {
    #[serde(borrow)]
    pub query: Box<Term<'a>>,
    pub hypotheses: Vec<Term<'a>>,
    pub variables: Vec<Variable<'a>>,
    pub actions: Vec<Action<'a>>,
    pub names: Vec<Name<'a>>,
    pub operators: Vec<Operator<'a>>,
    pub macros: Vec<Macro<'a>>,
    pub types: Vec<Sort<'a>>,
}

/// Same as [SquirrelDump] but with easier access to various field using [HashMap]s
///
/// `names`, `operators`, `macros` and `types` are [HashMap]s to make them efficiently seachable
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ProcessedSquirrelDump<'a> {
    query: Box<Term<'a>>,
    hypotheses: Vec<Term<'a>>,
    variables: Vec<Variable<'a>>,
    actions: HashMap<Path<'a>, Action<'a>>,
    names: HashMap<Path<'a>, FunctionType<'a>>,
    operators: HashMap<Path<'a>, operator::Data<'a>>,
    macros: HashMap<Path<'a>, mmacro::Data<'a>>,
    types: HashMap<Path<'a>, mtype::SortData>,
}

#[allow(dead_code)]
impl<'a> ProcessedSquirrelDump<'a> {
    pub fn query(&self) -> &Term<'a> {
        &self.query
    }

    pub fn hypotheses(&self) -> &[Term<'a>] {
        &self.hypotheses
    }

    pub fn variables(&self) -> &[Variable<'a>] {
        &self.variables
    }

    pub fn names(&self) -> &HashMap<Path<'a>, FunctionType<'a>> {
        &self.names
    }

    pub fn get_name(&self, k: &Path<'a>) -> Option<&FunctionType<'a>> {
        self.names.get(k)
    }

    pub fn operators(&self) -> &HashMap<Path<'a>, operator::Data<'a>> {
        &self.operators
    }

    pub fn get_operator(&self, k: &Path<'a>) -> Option<&operator::Data<'a>> {
        self.operators.get(k)
    }

    pub fn macros(&self) -> &HashMap<Path<'a>, mmacro::Data<'a>> {
        &self.macros
    }

    pub fn get_macro(&self, k: &Path<'a>) -> Option<&mmacro::Data<'a>> {
        self.macros.get(k)
    }

    pub fn types(&self) -> &HashMap<Path<'a>, mtype::SortData> {
        &self.types
    }

    pub fn get_type(&self, k: &Path<'a>) -> Option<&mtype::SortData> {
        self.types.get(k)
    }

    pub fn actions(&self) -> &HashMap<Path<'a>, Action<'a>> {
        &self.actions
    }

    pub fn get_action(&self, k: &Path<'a>) -> Option<&Action<'a>> {
        self.actions.get(k)
    }
}

impl<'a> From<SquirrelDump<'a>> for ProcessedSquirrelDump<'a> {
    fn from(
        SquirrelDump {
            query,
            hypotheses,
            variables,
            actions,
            names,
            operators,
            macros,
            types,
        }: SquirrelDump<'a>,
    ) -> Self {
        let names = convert_content_list(names);
        let operators = convert_content_list(operators);
        let macros = convert_content_list(macros);
        let types = convert_content_list(types);
        let actions = actions
            .into_iter()
            .map(|a| {
                let x = a.name.clone();
                (x, a)
            })
            .collect();

        Self {
            query,
            hypotheses,
            variables,
            actions,
            names,
            operators,
            macros,
            types,
        }
    }
}

fn convert_content_list<'a, U>(l: implvec!(Content<'a, U>)) -> HashMap<Path<'a>, U> {
    l.into_iter()
        .map(|Content { symb, data }| (symb, data))
        .collect()
}
