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
