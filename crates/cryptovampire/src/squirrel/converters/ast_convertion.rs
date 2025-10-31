use itertools::{Either, Itertools, chain};
use utils::all_or_one::AoOV;
use utils::monad::Monad;
use utils::string_ref::StrRef;
use utils::traits::NicerError;
use utils::vecref::VecRef;
use utils::{mdo, pure};

use super::helper_functions::*;
use super::{Context, RAoO};
use crate::formula::sort::builtins::{BOOL, MESSAGE, NAME, STEP};
use crate::parser::ast::{self, Options, Term};
use crate::squirrel::Sanitizable;
use crate::squirrel::converters::ContextBuilder;
use crate::squirrel::json::operator::{OperatorName, OperatorNameRef};
use crate::squirrel::json::{self, NameNameRef, mmacro};
use crate::{bail_at, error_at};

pub trait ToAst<'a> {
    type Target;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target>;
}

impl<'a> ToAst<'a> for json::Term<'a> {
    type Target = ast::Term<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Term::Fun { symb } => convert_function(symb, ctx),
            json::Term::Let { .. } => bail_at!(@ "no lets"),
            // actual work
            json::Term::Var { var } => {
                mdo!(pure ast::Application::from(var.sanitized(&ctx)).into())
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
            json::Term::Name { symb, args } => {
                let symb = NameNameRef(symb.path());
                convert_function_or_name_application::<_, OperatorName<'a>>(
                    Either::Left(&symb),
                    args,
                    ctx,
                )
            }
            json::Term::Macro {
                symb,
                args,
                timestamp,
            } => convert_macro_application(symb, args, timestamp, ctx),
            json::Term::Action { symb, args } => convert_action_application(symb, args, ctx),
        }
    }
}

pub const INDEX_SORT_NAME: &str = "index";
impl<'a> ToAst<'a> for json::sort::Type<'a> {
    type Target = ast::TypeName<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Type::Message => mdo!(pure MESSAGE.name().into()),
            json::Type::Boolean => mdo!(pure BOOL.name().into()),
            json::Type::Timestamp => mdo!(pure STEP.name().into()),
            json::Type::Index => mdo!(pure StrRef::from_static(INDEX_SORT_NAME).into()),
            json::Type::TBase(p) => {
                if let Some(true) = ctx.dump().get_type(p).map(|s| !s.can_be_index()) {
                    pure!(MESSAGE.name().into())
                } else {
                    pure!(p.sanitized(&ctx).into())
                }
            }
            json::Type::Tuple { .. } => pure!(MESSAGE.name().into()),
            json::Type::TVar { .. } | json::Type::TUnivar { .. } | json::Type::Fun { .. } => Err(
                error_at!(@ "unsupported argument: {}", serde_json::to_string_pretty(self).unwrap()),
            ),

            json::Type::Name => pure!(NAME.name().into()),
        }
        .debug_continue()
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
            globals,
        } = self;

        let name = ast::StepName::from(name.sanitized(&ctx));
        let args: Vec<_> = indices
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort().convert(ctx);
                    pure (var.sanitized(&ctx), sort)
                }
            })
            .try_collect()?;
        let assignements: Vec<_> = updates
            .iter()
            .map(|update| {
                json::action::UpdateRef {
                    action: self,
                    update,
                }
                .convert(ctx)
            })
            .try_collect()?;

        let options = Options::default();

        // FIXME: make this work
        assert!(
            condition.vars.is_empty(),
            "free variables in a condition (and I'm not sure what this means)"
        );

        let ctx = ContextBuilder::from(ctx)
            // .current_step(Some(self))
            .build()
            .unwrap();

        let fst_global_macro = globals
            .iter()
            .filter_map(|symb| {
                // FIXME: better deal with the option
                ctx.dump().get_macro(symb)
            })
            .next();

        mdo! {
            let! message = self.prepare_term(output.term(), fst_global_macro, ctx);
            let! condition = self.prepare_term(condition.term(), fst_global_macro, ctx);
            let! assignements = Ok(AoOV::transpose_iter(assignements.clone()));
            let! args = Ok(AoOV::transpose_iter(args.clone()));
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

impl<'a> json::Action<'a> {
    /// This adds `let..in` in from of a term so that the global macros may be properly defined
    fn prepare_term<'b>(
        &self,
        term: &json::Term<'a>,
        fst_global_macro: Option<&mmacro::Data<'a>>,
        ctx: Context<'b, 'a>,
    ) -> RAoO<ast::Term<'a, StrRef<'a>>> {
        let output = term.convert(ctx).bind(|term| {
            fst_global_macro
                .iter()
                .flat_map(|g| g.inputs().rev().enumerate())
                .map(|(i, v)| {
                    let a = ctx
                        .dump()
                        .get_action_from_action_v(&self.action[0..i])
                        .ok_or_else(|| {
                            let actions = self.action[0..i]
                                .iter()
                                .map(serde_json::to_string_pretty)
                                .map(Result::unwrap)
                                .join(";\n");
                            error_at!(@ "cannot find an action from its shape while \
                            building the output of {:}\n{actions}", self.name().sanitized(&ctx),
                            )
                        })?;
                    Ok((
                        v,
                        json::Term::Macro {
                            symb: json::path::ISymb::input(),
                            args: vec![],
                            timestamp: Box::new(a.as_term()),
                        },
                    ))
                })
                .try_fold(AoOV::pure(term), |acc, t: crate::Result<_>| {
                    let (var, input) = t?;
                    mdo! {
                        let! acc = Ok(acc);
                        let! input = input.convert(ctx);
                        let! sort = var.sort().convert(ctx);
                        let var = (var.sanitized(&ctx), sort).into();
                        pure Term::letin(var, input.clone(), acc.clone())
                    }
                })
        });
        output
    }
}

impl<'a, 'b> ToAst<'a> for json::action::UpdateRef<'a, 'b> {
    type Target = ast::Assignement<'a, StrRef<'a>>;

    fn convert<'c>(&self, ctx: Context<'c, 'a>) -> RAoO<Self::Target> {
        let Self {
            action,
            update: json::action::Update { symb, args, body },
        } = self;

        // let cell = apply_fun(symb.clone(), args, ctx)?;
        let fresh_vars: Vec<_> = args
            .iter()
            .flat_map(|t| t.vars())
            .filter(|v| !action.indices.contains(v))
            .map(|var| {
                mdo! {
                    let! sort = var.sort().convert(ctx);
                    pure (ast::Variable::from(var.sanitized(&ctx)), sort)
                }
            })
            .try_collect()?;
        let args: Vec<_> = args.iter().map(|arg| arg.convert(ctx)).try_collect()?;
        mdo! {
            let! args = Ok(AoOV::transpose_iter(args));
            let! fresh_vars = Ok(AoOV::transpose_iter(fresh_vars.clone()));
            let! term = body.convert(ctx);
            pure ast::Assignement {
                span: Default::default(),
                cell: ast::Application::new_app(Default::default(),  symb.sanitized(&ctx), args.clone()),
                term,
                fresh_vars: {
                    if fresh_vars.is_empty() {
                        None
                    } else {
                        Some(fresh_vars.iter().cloned().collect())
                    }
                }
            }
        }
    }
}

/// *danger*
///
/// The way global macros are handeled in `squirrel` is... wierd. Notably they
/// behave wierdly with reguards to `input`s.
/// ~I have to delay dealing with it
/// the moment I apply a macro. Hence most of the logic is in
/// [convert_macro_application].~
/// I moved it to [json::Action::convert]
///
/// A macro signature is (indices ++ inputs ++ [time]).
impl<'a, 'c> ToAst<'a> for json::MacroRef<'a, 'c> {
    type Target = Option<ast::Macro<'a, StrRef<'a>>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        use json::mmacro::*;
        let json::ContentRef { symb, data } = self;
        match data {
            Data::Global(
                g @ GlobalMacro {
                    arity: _,
                    sort: _,
                    data:
                        GlobalData {
                            indices,
                            ts,
                            body,
                            inputs: _, // called someway else
                            action: _,
                            ty: _,
                        },
                },
            ) => {
                mdo! {
                    let! res = ConcreteMacro {
                        symb: OperatorNameRef(&symb.0),
                        body,
                        args: chain!(indices.iter(), g.inputs(), [ts].into_iter()).collect()
                    }.convert(ctx);
                    pure Some(res)
                }
            }
            _ => pure!(None),
        }
    }
}

pub struct ConcreteMacro<'a, 'b> {
    pub symb: OperatorNameRef<'a, 'b>,
    pub body: &'b json::Term<'a>,
    pub args: VecRef<'b, json::Variable<'a>>,
}

impl<'a, 'b> ToAst<'a> for ConcreteMacro<'a, 'b> {
    type Target = ast::Macro<'a, StrRef<'a>>;

    fn convert<'c>(&self, ctx: Context<'c, 'a>) -> RAoO<Self::Target> {
        let Self { symb, body, args } = self;

        let args: Vec<_> = args
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort().convert(ctx);
                    pure (var.sanitized(&ctx), sort)
                }
            })
            .try_collect()?;
        mdo! {
            let! args = Ok(AoOV::transpose_iter(args));
            let! term = body.convert(ctx);
            pure ast::Macro {
                span: Default::default(),
                name: symb.sanitized(&ctx).into(),
                args:args.iter().cloned().collect(),
                term,
                options: Options::default()
            }
        }
    }
}
