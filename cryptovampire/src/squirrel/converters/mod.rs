use std::fmt::Display;

use ast_convertion::{ConcreteMacro, ToAst, INDEX_SORT_NAME};
use cryptovampire_lib::formula::function::builtin::{
    AND, EMPTY, EQUALITY, FALSE, FALSE_F, HAPPENS, IMPLIES, LESS_THAN_EQ_STEP, LESS_THAN_STEP, NOT, OR, PRED, TRUE, TRUE_F
};
use hashbrown::{HashMap, HashSet};
use itertools::{chain, Itertools};
use log::trace;
use serde::Serialize;
use static_init::dynamic;
use utils::{
    all_or_one::{AllOrOneShape, AoOV},
    mdo,
    monad::Monad,
    string_ref::StrRef,
};

use crate::{
    bail_at,
    parser::{ast, InputError},
    squirrel::json::{self, MacroRef, Pathed},
};

/// Functions that already exists in cv and need to be renamed
#[dynamic]
static BUILTIN_FUNCTIONS: HashMap<&'static str, StrRef<'static>> = {
    [
        ("&&", AND.name()),
        ("and", AND.name()),
        ("||", OR.name()),
        ("or", OR.name()),
        ("<=>", EQUALITY.name()),
        ("=>", IMPLIES.name()),
        ("=", EQUALITY.name()),
        ("<=", LESS_THAN_EQ_STEP.name()),
        ("<", LESS_THAN_STEP.name()),
        ("not", NOT.name()),
        ("true", TRUE_F.name()),
        ("false", FALSE_F.name()),
        ("empty", EMPTY.name()),
        ("ø", EMPTY.name()),
        ("happens", HAPPENS.name()),
        ("pred", PRED.name()),
    ]
    .into_iter()
    .collect()
};

/// Functions will break things if they are called as functions
#[dynamic]
static FORBIDDEN_FUNCTIONS: HashSet<&'static str> =
    ["diff", ">", ">=", "att", "qatt"].into_iter().collect();

use super::{
    json::{ProcessedSquirrelDump, SquirrelDump},
    Sanitizer,
};
type RAoO<T> = Result<AoOV<T>, InputError>;

mod ast_convertion;
mod helper_functions;

/// see [mk_depends_mutex_lemmas]
mod convert_order;

pub use top_level_converter::convert_squirrel_dump;
mod top_level_converter;

// FIXME: do it better
const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static("_$tuple");
const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$fst");
const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$snd");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Context<'a, 'str> {
    pub shape: AllOrOneShape,
    pub dump: &'a ProcessedSquirrelDump<'str>,
    pub builtin_function: &'static HashMap<&'static str, StrRef<'static>>,
    pub forbidden_function: &'static HashSet<&'static str>,
}

impl<'a, 'str> Context<'a, 'str> {
    pub fn new(dump: &'a ProcessedSquirrelDump<'str>) -> Self {
        Self {
            shape: AllOrOneShape::Any(()),
            dump,
            builtin_function: &BUILTIN_FUNCTIONS,
            forbidden_function: &FORBIDDEN_FUNCTIONS,
        }
    }

    pub fn dump(&self) -> &ProcessedSquirrelDump<'str> {
        self.dump
    }

    pub fn shape(&self) -> AllOrOneShape {
        self.shape
    }
}

impl<'a, 'str> Sanitizer for Context<'a, 'str> {
    fn sanitize<'b>(&self, str: &StrRef<'b>) -> StrRef<'b> {
        self.builtin_function
            .get(str.as_ref())
            .unwrap_or(str)
            .clone()
    }
}

trait MDebugIter<U> {
    fn debug(self, msg:impl Display+'static) -> impl Iterator<Item = U>;
}

impl<I, S> MDebugIter<S> for I
where
    I: Iterator<Item = S>,
    S: Serialize,
{
    fn debug(self, msg: impl Display+'static) -> impl Iterator<Item = S> {
        self.map(move |x| {
            trace!(
                "{msg}{}",
                serde_json::to_string_pretty(&x).unwrap()
            );
            x
        })
    }
}
