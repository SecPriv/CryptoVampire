use ast_convertion::{ConcreteMacro, Context, ToAst, INDEX_SORT_NAME};
use itertools::{chain, Itertools};
use utils::{all_or_one::AoOV, mdo, monad::Monad, string_ref::StrRef};

use crate::{
    bail_at,
    parser::{ast, InputError},
    squirrel::json::{self, MacroRef, Pathed},
};

use super::json::{ProcessedSquirrelDump, SquirrelDump};
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