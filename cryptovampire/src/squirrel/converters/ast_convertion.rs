// FIXME: do it better
pub const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static("_$tuple");
pub const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$fst");
pub const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$snd");

use cryptovampire_lib::formula::sort::builtins::{BOOL, MESSAGE, STEP};
use itertools::{chain, Itertools};
use utils::{
    all_or_one::{AllOrOneShape, AoOV},
    mdo,
    monad::Monad,
    pure,
    string_ref::StrRef,
};

use crate::{
    bail_at, err_at,
    parser::{
        ast::{self, Options},
        Location,
    },
    squirrel::json::{self, Named, Pathed, ProcessedSquirrelDump},
};

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

impl<'a> ToAst<'a> for json::Action<'a> {
    type Target = ast::Step<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        let Self {
            name,
            indices,
            condition,
            updates,
            output,
            action: _,
            input: _,
            globals: _,
        } = self;

        let name = ast::StepName::from(name.equiv_name_ref());
        let args: Vec<_> = indices
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort.convert(ctx);
                    pure (var.id.name().drop_guard(), sort)
                }
            })
            .try_collect()?;
        let assignements: Vec<_> = updates.iter().map(|upd| upd.convert(ctx)).try_collect()?;

        let options = Options::default();

        // FIXME: make this work
        assert!(
            condition.vars.is_empty(),
            "free variables in a condition (and I'm not sure what this means)"
        );

        mdo! {
            let! message = output.term.convert(ctx);
            let! condition = condition.term.convert(ctx);
            let! assignements = Ok(AoOV::transpose(assignements.clone()));
            let! args = Ok(AoOV::transpose(args.clone()));
            pure ast::Step {
                name: name.clone(),
                span: Default::default(),
                args: args.into_iter().collect(),
                condition: condition.clone(),
                message: message.clone(),
                assignements: Some(assignements.iter().cloned().collect()),
                options: options.clone()
            }
        }
    }
}

impl<'a> ToAst<'a> for json::action::Update<'a> {
    type Target = ast::Assignement<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        let Self { symb, args, body } = self;

        // let cell = apply_fun(symb.clone(), args, ctx)?;
        let args: Vec<_> = args.iter().map(|arg| arg.convert(ctx)).try_collect()?;
        mdo! {
            let! args = Ok(AoOV::transpose(args));
            let! term = body.convert(ctx);
            pure ast::Assignement {
                span: Default::default(),
                cell: ast::Application::new_app(symb.clone().drop_guard(), args.clone()),
                term,
                fresh_vars: None
            }
        }
    }
}

impl<'a> ToAst<'a> for json::Macro<'a> {
    type Target = Option<ast::Macro<'a, StrRef<'a>>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        use json::mmacro::*;
        let json::Content { symb, data } = self;
        match data {
            Data::Global(GlobalMacro {
                arity: _,
                sort: _,
                data:
                    GlobalData {
                        inputs,
                        indices,
                        ts,
                        body,
                        action:_,
                        ty:_,
                    },
            }) => {
                let args: Vec<_> = chain!(indices.iter(), inputs.iter(), [ts])
                    .map(|var| {
                        mdo! {
                            let! sort = var.sort.convert(ctx);
                            pure (var.id.name().drop_guard(), sort)
                        }
                    })
                    .try_collect()?;
                mdo! {
                    let! args = Ok(AoOV::transpose(args));
                    let! term = body.convert(ctx);
                    pure Some(ast::Macro {
                        span: Location::default(),
                        name: symb.equiv_name_ref().into(),
                        args:args.iter().cloned().collect(),
                        term,
                        options: Options::default()
                    })
                }
            }
            _ => pure!(None),
        }
    }
}
