// FIXME: do it better
pub const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static("_$tuple");
pub const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$fst");
pub const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$snd");

use cryptovampire_lib::formula::{
    function::builtin::EMPTY_FUN_NAME,
    sort::builtins::{BOOL, MESSAGE, STEP},
};
use if_chain::if_chain;
use itertools::{chain, Itertools};
use utils::{
    all_or_one::{AllOrOne, AllOrOneShape, AoOV},
    implvec, mdo,
    string_ref::StrRef,
};

use crate::{
    bail_at, err_at,
    parser::{
        ast::{self, FindSuchThat, Term, TypedArgument},
        FromStaticString, InputError,
    },
    squirrel::{
        converters::helper_functions::to_variable_binding,
        json::{self, mmacro, Named, Pathed, ProcessedSquirrelDump},
    },
};

use utils::monad::Monad;

use super::{helper_functions::*, RAoO};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Context<'a, 'str> {
    pub shape: AllOrOneShape,
    pub dump: &'a ProcessedSquirrelDump<'str>,
}

impl<'a, 'str> Context<'a, 'str> {
    pub fn new(dump: &'a ProcessedSquirrelDump<'str>) -> Self {
        Self {
            shape: AllOrOneShape::Any(()),
            dump,
        }
    }

    pub fn dump(&self) -> &ProcessedSquirrelDump<'str> {
        self.dump
    }

    pub fn shape(&self) -> AllOrOneShape {
        self.shape
    }
}

pub trait ToAst<'a> {
    type Target;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target>;
}

impl<'a> ToAst<'a> for json::Term<'a> {
    type Target = ast::Term<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Term::Fun { .. } => {
                bail_at!(@ "no high order")
            }
            json::Term::Let { .. } => bail_at!(@ "no lets"),
            // actual work
            json::Term::Var { var } => {
                mdo!(pure ast::Application::from(var.name().drop_guard()).into())
            }
            json::Term::Tuple { elements } => convert_tuple(elements, ctx),
            json::Term::Quant {
                quantificator,
                vars,
                body,
            } => convert_quantifier(quantificator, vars, body, ctx),
            json::Term::Find {
                vars,
                condition,
                success,
                faillure,
            } => convert_findst(vars, condition, success, faillure, ctx),
            json::Term::Proj { id, body } => convert_projection(*id, body, ctx),
            json::Term::Diff { terms } => convert_diff(terms, ctx),
            json::Term::App { f, args } => convert_application(f, args, ctx),
            json::Term::Name { symb, args } => convert_name_application(symb, args, ctx),
            json::Term::Macro {
                symb,
                args,
                timestamp,
            } => convert_macro_application(symb, args, timestamp, ctx),
            json::Term::Action { symb, args } => convert_action_application(symb, args, ctx),
        }
    }
}


impl<'a> ToAst<'a> for json::sort::Type<'a> {
    type Target = ast::TypeName<'a, StrRef<'a>>;

    fn convert<'b>(&self, _: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Type::Message => mdo!(pure MESSAGE.name().into()),
            json::Type::Boolean => mdo!(pure BOOL.name().into()),
            json::Type::Timestamp => mdo!(pure STEP.name().into()),
            json::Type::Index => mdo!(pure StrRef::from_static("index").into()),
            json::Type::TBase(p) => mdo!(pure p.equiv_name_ref().into()),
            json::Type::TVar { .. }
            | json::Type::TUnivar { .. }
            | json::Type::Tuple { .. }
            | json::Type::Fun { .. } => Err(err_at!(@ "arg")),
        }
    }
}
