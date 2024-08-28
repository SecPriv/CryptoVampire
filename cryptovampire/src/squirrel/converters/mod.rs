use std::fmt::Display;

use ast_convertion::{ConcreteMacro, ToAst, INDEX_SORT_NAME};
use base64::Engine;
use cryptovampire_lib::formula::function::builtin::{
    AND, EMPTY, EQUALITY, FALSE_F, HAPPENS, IMPLIES, LESS_THAN_EQ_STEP, LESS_THAN_STEP, NOT, OR,
    PRED, TRUE_F,
};
use derive_builder::Builder;
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
    squirrel::json::{self, MacroRef, Pathed,},
    // squirrel::Sanitizable
};


/// Functions who name is fixed
/// 
/// When the symbol's [Sanitizable::to_str_ref] is in the keys,
/// then we use the associated value
/// 
/// [Sanitizable]: crate::squirrel::Sanitizable
#[dynamic]
static REMMAPPED_FUNCTION: HashMap<&'static str, StrRef<'static>> = {
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
        // ("xor", "_$xor".into()),
        ("init", "init".into()),
        (DEFAULT_TUPLE_NAME_NAME, DEFAULT_TUPLE_NAME.clone()),
        (DEFAULT_FST_PROJ_NAME_NAME, DEFAULT_FST_PROJ_NAME.clone()),
        (DEFAULT_SND_PROJ_NAME_NAME, DEFAULT_SND_PROJ_NAME.clone()),
        ("input", "input".into())
    ]
    .into_iter()
    .collect()
};

/// Functions will break things if they are called as functions
#[dynamic]
static FORBIDDEN_FUNCTIONS: HashSet<&'static str> =
    ["diff", ">", ">=", "att", "qatt"].into_iter().collect();

/// Symbols that should not be decalred
#[dynamic]
static BUILTIN_FUNCTION: HashSet<&'static str> = [
    "&&", "||", "and", "or", "<=>", "=>", "=", "<=", "<", "not", "true",
    "false", "empty", "ø", "happens", "pred"
]
.into_iter()
.collect();

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

const DEFAULT_TUPLE_NAME_NAME: &'static str = "pair";
const DEFAULT_FST_PROJ_NAME_NAME: &'static str = "fst";
const DEFAULT_SND_PROJ_NAME_NAME: &'static str = "snd";

const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static(&DEFAULT_TUPLE_NAME_NAME);
const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static(&DEFAULT_FST_PROJ_NAME_NAME);
const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static(&DEFAULT_SND_PROJ_NAME_NAME);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Builder)]
#[builder(name = "ContextBuilder")]
struct Context<'a, 'str> {
    #[builder(default)]
    shape: AllOrOneShape,
    dump: &'a ProcessedSquirrelDump<'str>,
    // #[builder(default)]
    // current_step: Option<&'a json::Action<'str>>,
}

impl<'a, 'str> From<Context<'a, 'str>> for ContextBuilder<'a, 'str> {
    fn from(
        Context {
            shape,
            dump,
            // current_step,
        }: Context<'a, 'str>,
    ) -> Self {
        let mut ctx = ContextBuilder::create_empty();
        ctx.shape(shape).dump(dump)/* .current_step(current_step) */;
        ctx
    }
}

impl<'a, 'str> Context<'a, 'str> {
    pub fn dump(&self) -> &ProcessedSquirrelDump<'str> {
        self.dump
    }

    pub fn shape(&self) -> AllOrOneShape {
        self.shape
    }

    // fn current_step(&self) -> Option<&'a json::Action<'str>> {
    //     self.current_step
    // }

    fn remmaped_function(&self) -> &'static HashMap<&'static str, StrRef<'static>> {
        &REMMAPPED_FUNCTION
    }

    fn forbidden_function(&self) -> &'static HashSet<&'static str> {
        &FORBIDDEN_FUNCTIONS
    }

    fn builtin_function(&self) -> &'static HashSet<&'static str> {
        &BUILTIN_FUNCTION
    }
}

static SMT_SAFE: Result<base64::engine::GeneralPurpose, base64::alphabet::ParseAlphabetError> = {
    match base64::alphabet::Alphabet::new(
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789#$",
    ) {
        Ok(a) => Ok(base64::engine::GeneralPurpose::new(
            &a,
            base64::engine::general_purpose::NO_PAD,
        )),
        Err(e) => Err(e),
    }
};

impl<'a, 'str> Sanitizer for Context<'a, 'str> {
    fn sanitize<'b, S: super::Sanitizable<'b>>(&self, str: &S) -> StrRef<'b> {
        let str_ref = str.to_str_ref();
        self.remmaped_function()
            .get(str_ref.as_str())
            .cloned()
            .unwrap_or_else(|| {
                let str_ref = if str_ref.chars().all(|s| s.is_alphanumeric()) {
                    str_ref.as_str()
                } else {
                    let encoded = SMT_SAFE.as_ref().unwrap().encode(str_ref.as_str());
                    &format!("$base64${encoded}")
                };
                format!("{:}{str_ref}", str.sanitize_kind()).into()
            })
    }
    // fn sanitize<'b>(&self, str: &StrRef<'b>) -> StrRef<'b> {
    //     // self.builtin_function()
    //     //     .get(str.as_ref())
    //     //     .unwrap_or(str)
    //     //     .clone()
    // }
}

trait MDebugIter<U> {
    fn debug(self, msg: impl Display + 'static) -> impl Iterator<Item = U>;
}

impl<I, S> MDebugIter<S> for I
where
    I: Iterator<Item = S>,
    S: Serialize,
{
    fn debug(self, msg: impl Display + 'static) -> impl Iterator<Item = S> {
        self.map(move |x| {
            trace!("{msg}{}", serde_json::to_string_pretty(&x).unwrap());
            x
        })
    }
}
