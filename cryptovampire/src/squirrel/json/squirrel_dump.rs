use std::{hash::Hash, sync::Arc};

use hashbrown::HashMap;
use paste::paste;
use serde::{Deserialize, Serialize};
use utils::implvec;

use super::*;

// // for the documentation
// #[cfg(doc)]
// use super::action::ActionV;

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
    actions: HashMap<Path<'a>, Arc<Action<'a>>>,
    actions_from_action_v: HashMap<action::ActionV<'a>, Arc<Action<'a>>>,
    names: HashMap<Path<'a>, FunctionType<'a>>,
    operators: HashMap<Path<'a>, operator::Data<'a>>,
    macros: HashMap<Path<'a>, mmacro::Data<'a>>,
    types: HashMap<Path<'a>, mtype::SortData>,
}

/// Make getter for most of the [HashMap]-based field. It generate getters to get
/// an iterator over the elements with or without the [Path], and to fetch a single
/// element.
///
/// `name` is the name of the field *in singular*, the macro will turn in into plural
/// on its own
macro_rules! mk_getters {
    ($name:ident : $t:ty) => {
        paste! {
            #[doc="get the an [Iterator] of [<$name s>]"]
            pub fn [<$name s>]<'b>(&'b self) -> impl Iterator<Item = &'b $t> {
                self.[<$name s>].values()
            }

            #[doc="get the an [Iterator] of [<$name s>] with its symbol"]
            pub fn [<$name s_with_symb>]<'b>(&'b self) -> impl Iterator<Item = (&'b Path<'a>, &'b $t)> {
                self.[<$name s>].iter()
            }

            #[doc="get a specific $name"]
            pub fn [<get_$name>](&self, symb: &Path<'a>) -> Option<&$t> {
                self.[<$name s>].get(symb)
            }
        }
    };
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

    mk_getters!(name: FunctionType<'a>);
    mk_getters!(operator: operator::Data<'a>);
    mk_getters!(macro: mmacro::Data<'a>);
    mk_getters!(type: mtype::SortData);

    /// Get the [FunctionType] associated to an [Operator] or a [Name] given it's
    /// [Path]. It returns [None] if it cannot find either.
    ///
    /// **NB**: this will look for an [Operator] first
    pub fn get_name_or_operator_fun_type(&self, symb: &Path<'a>) -> Option<&FunctionType<'a>> {
        self.get_operator(symb)
            .map(|o| &o.sort)
            .or_else(|| self.get_name(symb))
    }

    pub fn actions<'b>(&'b self) -> impl Iterator<Item = &'b Action<'a>> {
        self.actions_with_symb().map(|(_, y)| y)
    }

    pub fn actions_with_symb<'b>(&'b self) -> impl Iterator<Item = (&'b Path<'a>, &'b Action<'a>)> {
        self.actions.iter().map(|(x, y)| (x, Arc::as_ref(y)))
    }

    pub fn get_action(&self, k: &Path<'a>) -> Option<&Action<'a>> {
        self.actions.get(k).map(Arc::as_ref)
    }

    /// Try to mach some magic the magic `squirrel` to use
    /// [ActionV] to find an [Action]. The type of `v` corresponds to an
    /// [ActionV] using a slice instead of a [Vec].
    ///
    /// [ActionV]: super::action::ActionV
    pub fn get_action_from_action_v(
        &self,
        v: &[action::Item<Vec<Variable<'a>>>],
    ) -> Option<&Action<'a>> {
        self.actions_from_action_v.get(v).map(Arc::as_ref)
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
        let actions: HashMap<_, _> = actions
            .into_iter()
            .map(|a| {
                let x = a.name.clone();
                (x, Arc::new(a))
            })
            .collect();
        let actions_from_action_v = actions
            .values()
            .map(|a| (a.action.clone(), Arc::clone(a)))
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
            actions_from_action_v,
        }
    }
}

fn convert_content_list<'a, U>(l: implvec!(Content<'a, U>)) -> HashMap<Path<'a>, U> {
    l.into_iter()
        .map(|Content { symb, data }| (symb, data))
        .collect()
}
