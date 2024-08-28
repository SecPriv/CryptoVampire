use itertools::Itertools;
use utils::{all_or_one::AoOV, implvec, mdo, string_ref::StrRef};

use crate::{
    err_at,
    parser::ast::{self, TypedArgument},
    squirrel::{
        converters::ast_convertion::ToAst,
        json::{self}, Sanitizable,
    },
};

use utils::monad::Monad;

use super::Context;
use super::RAoO;

pub use convertion_functions::*;

mod convertion_functions;

pub fn apply_fun<'a, 'b, 'c>(
    fun: StrRef<'a>,
    args: implvec!(&'b json::Term<'a>),
    ctx: Context<'c, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>>
where
    'a: 'b,
{
    let args: Vec<_> = args.into_iter().map(|arg| arg.convert(ctx)).try_collect()?;
    mdo! {
        let! args = Ok(AoOV::transpose_iter(args));
        pure ast::Application::new_app(fun.clone(), args).into()
    }
}

/// Turn a list of [json::Term] that should only contain [json::Term::Var] into a [ast::TypedArgument]
pub fn to_variable_binding<'a, 'b>(
    vars: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<TypedArgument<'a, StrRef<'a>>> {
    let mut res = Ok(()); // to keep track if something went wrong

    let iter = vars
        .iter()
        .map(|t| match t {
            json::Term::Var { var } => Ok(var),
            _ => Err(err_at!(@ "not a variable")),
        })
        .map(|x| {
            x.and_then(|var| {
                mdo! {
                    let! sort = var.sort().convert(ctx);
                    pure (var.sanitized(&ctx), sort)
                }
            })
        })
        .filter_map(|x| match x {
            Ok(v) => Some(v),
            Err(e) => {
                res = Err(e);
                None
            }
        });

    let out = AoOV::transpose_iter(iter); // save the temporary result to update `res`
    mdo! {
        let! res = res.map(|_| out);
        pure res.into_iter().collect()
    }
}

pub fn transpose_raov<U>(arg: RAoO<Option<U>>) -> Option<RAoO<U>> {
    arg.map(|arg| arg.transpose()).transpose()
}
