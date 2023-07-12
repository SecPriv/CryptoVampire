use std::collections::HashMap;

use super::{
    ast::{ASTList, Declaration, DeclareType, AST},
    *,
};
use crate::{
    container::Container,
    formula::{sort::{InnerSort, Sort}, function::Function},
    implvec,
};

#[derive(Debug)]
pub struct Environement<'bump, 'str> {
    container: &'bump Container<'bump>,
    ast: ASTList<'str>,

    sort_hash: HashMap<&'bump str, Sort<'bump>>,
    function_hash: HashMap<&'bump str, Function<'str>>
}

pub fn declare_sorts<'a, 'bump>(env: &mut Environement<'bump, 'a>) -> Result<(), E> {
    env.ast
        .into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(d) => match d.as_ref() {
                Declaration::Type(dt) => Some(dt),
                _ => None,
            },
            _ => None,
        })
        .try_for_each(|s| {
            let name = s.name();
            if env.sort_hash.contains_key(name) {
                err(merr!(*s.get_name_span(); "the sort name {} is already in use", name))
            } else {
                let sort = Sort::new_regular(env.container, name.to_owned());
                env.sort_hash.insert(sort.name(), sort)
                .ok_or_else(|| merr!(*s.get_name_span(); 
                        "!UNREACHABLE!(line {} in {}) The sort name {} somehow reintroduced itself in the hash", line!(), file!(), name))
                .map(|_|())
            }
        })
}

pub fn declare_functions<'a, 'bump>(env: &mut Environement<'bump, 'a>) -> Result<(), E> {


    todo!()
}