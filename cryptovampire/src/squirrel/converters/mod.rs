use ast_convertion::ToAst;
use itertools::{chain, Itertools};
use utils::{all_or_one::AoOV, string_ref::StrRef};

use crate::parser::{ast, InputError};

use super::json::{ProcessedSquirrelDump, SquirrelDump};
type RAoO<T> = Result<AoOV<T>, InputError>;

mod ast_convertion;

fn convert_squirrel_dump<'a>(dump: SquirrelDump<'a>) -> RAoO<ast::ASTList<'a, StrRef<'a>>> {
    let pdump = &ProcessedSquirrelDump::from(dump);

    let ctx = ast_convertion::Context::new(pdump);

    // let mut asts = Vec::new();

    // let query = dump.query.convert(ctx)?;
    // let hypothesis: Vec<_> = dump
    //     .hypotheses
    //     .iter()
    //     .map(|h| h.convert(ctx))
    //     .try_collect()?;

    todo!()
}

mod helper_functions;