use std::hash::Hash;
use std::sync::Arc;

use action::ActionName;
use hashbrown::{Equivalent, HashMap};
use itertools::Either;
use mmacro::MacroName;
use mtype::SortName;
use operator::OperatorName;
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
    actions: HashMap<ActionName<'a>, Arc<Action<'a>>>,
    actions_from_action_v: HashMap<action::ActionV<'a>, Arc<Action<'a>>>,
    names: HashMap<NameName<'a>, FunctionType<'a>>,
    operators: HashMap<OperatorName<'a>, operator::Data<'a>>,
    macros: HashMap<MacroName<'a>, mmacro::Data<'a>>,
    types: HashMap<SortName<'a>, mtype::SortData>,
}

/// Make getter for most of the [HashMap]-based field. It generate getters to get
/// an iterator over the elements with or without the [Path], and to fetch a single
/// element.
///
/// `name` is the name of the field *in singular*, the macro will turn in into plural
/// on its own
macro_rules! mk_getters {
    ($name:ident : $nname:ty => $t:ty) => {
        paste! {
            #[doc="get the an [Iterator] of [<$name s>]"]
            pub fn [<$name s>](&self) -> impl Iterator<Item = &'_ $t> {
                self.[<$name s>].values()
            }

            #[doc="get the an [Iterator] of [<$name s>] with its symbol"]
            pub fn [<$name s_with_symb>]<'b>(&'b self) -> impl Iterator<Item = (&'b $nname, &'b $t)> {
                self.[<$name s>].iter()
            }

            #[doc="get a specific $name"]
            pub fn [<get_$name>]<K>(&self, symb: &K) -> Option<&$t> where K: hashbrown::Equivalent<$nname> + Hash {
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

    mk_getters!(name:NameName<'a> => FunctionType<'a>);
    mk_getters!(operator: OperatorName<'a> => operator::Data<'a>);
    mk_getters!(macro: MacroName<'a> => mmacro::Data<'a>);
    mk_getters!(type: SortName<'a> =>  mtype::SortData);

    /// Get the [FunctionType] associated to an [Operator] or a [Name] given it's
    /// [Path]. It returns [None] if it cannot find either.
    ///
    /// **NB**: this will look for an [Operator] first
    pub fn get_name_or_operator_fun_type<N, O>(
        &self,
        symb: Either<&N, &O>,
    ) -> Option<&FunctionType<'a>>
    where
        N: Equivalent<NameName<'a>> + std::hash::Hash,
        O: Equivalent<OperatorName<'a>> + std::hash::Hash,
    {
        match symb {
            Either::Left(name) => self.get_name(name),
            Either::Right(op) => self.get_operator(op).map(|o| &o.sort),
        }
        // self.inner_get_operator(symb.borrow())
        //     .map(|o| &o.sort)
        //     .or_else(|| self.inner_get_name(symb.borrow()))
    }

    pub fn actions<'b>(&'b self) -> impl Iterator<Item = &'b Action<'a>> + Clone {
        self.actions_with_symb().map(|(_, y)| y)
    }

    pub fn actions_with_symb<'b>(
        &'b self,
    ) -> impl Iterator<Item = (&'b ActionName<'a>, &'b Action<'a>)> + Clone {
        self.actions.iter().map(|(x, y)| (x, Arc::as_ref(y)))
    }

    pub fn get_action(&self, k: &ActionName<'a>) -> Option<&Action<'a>> {
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

fn convert_content_list<N: Hash + Eq, U>(l: implvec!(Content<N, U>)) -> HashMap<N, U> {
    l.into_iter()
        .map(|Content { symb, data }| (symb, data))
        .collect()
}
