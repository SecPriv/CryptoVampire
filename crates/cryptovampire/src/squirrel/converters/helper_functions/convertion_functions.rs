use std::borrow::Cow;

use hashbrown::Equivalent;
use if_chain::if_chain;
use itertools::{Either, Itertools, chain};
use log::trace;
use utils::all_or_one::AoOV;
use utils::monad::Monad;
use utils::string_ref::StrRef;
use utils::{match_as_trait, mdo, pure};

use super::super::{Context, RAoO};
use super::apply_fun;
use crate::formula::function::builtin::EMPTY_FUN_NAME;
use crate::parser::ast::{self, FindSuchThat, Operation, Term};
use crate::squirrel::Sanitizable;
use crate::squirrel::converters::ast_convertion::ToAst;
use crate::squirrel::converters::helper_functions::to_variable_binding;
use crate::squirrel::converters::{
    DEFAULT_FST_PROJ_NAME, DEFAULT_SND_PROJ_NAME, DEFAULT_TUPLE_NAME,
};
use crate::squirrel::json::action::ActionName;
use crate::squirrel::json::mmacro::{self, MacroNameRef};
use crate::squirrel::json::operator::OperatorName;
use crate::squirrel::json::{self, NameName};
use crate::{bail_at, err_at, error_at};

pub fn convert_application<'a, 'b>(
    f: &json::Term<'a>,
    args: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    match f {
        json::Term::Fun { symb } => {
            convert_function_or_name_application::<NameName<'a>, _>(Either::Right(symb), args, ctx)
        }
        json::Term::Macro { .. }
        | json::Term::App { .. }
        | json::Term::Var { .. }
        | json::Term::Let { .. }
        | json::Term::Tuple { .. }
        | json::Term::Proj { .. }
        | json::Term::Diff { .. }
        | json::Term::Find { .. }
        | json::Term::Name { .. }
        | json::Term::Action { .. }
        | json::Term::Quant { .. } => err_at!(@ "no high order"),
    }
}

/// Convert the application of a function.
///
/// The trickiest point of the functio is to take care of functions that take
/// tuples as arguments. There is a discrepency between `squirrel` and `cryptovampire`
/// with that regard. `squirrel` uses tuples to avoid partial application of certain
/// cryptographic function (e.g., `enc`); there is no such problem in `cryptovampire`
/// so such a work around was never implemented, and I'm not planning to implement one.
pub fn convert_function_or_name_application<'a, 'b, N, O>(
    symb: Either<&N, &O>,
    args: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>>
where
    N: Equivalent<NameName<'a>> + std::hash::Hash + Sanitizable<'a>,
    O: Equivalent<OperatorName<'a>> + std::hash::Hash + Sanitizable<'a>,
{
    let args: Vec<_> = if_chain! {
        if let Some(f) = ctx.dump().get_name_or_operator_fun_type(symb);
        let args_type = f.args.as_slice();
        if args_type.len() == 1;
        if let Some(json::sort::Type::Tuple {..}) = args_type.first();
        if let Some(json::Term::Tuple { elements }) = args.first();
        then { elements } // If it uses tuples as argument, we collapse it
        else { args }
    }
    .iter()
    .map(|arg| arg.convert(ctx))
    .try_collect()?;
    let symb = match_as_trait!(symb => {Either::Left(x) | Either::Right(x) => {x.sanitized(&ctx)}});
    // let op = Operation::get_operation(symb.as_str());
    mdo! {
        let! args = Ok(AoOV::transpose_iter(args));
        // pure if let Some(operation) = op {
        //     ast::Infix{span: Default::default(), operation, terms: args}.into()
        // } else {
        //     ast::Application::new_app(symb.clone(), args).into()
        // }
        pure match symb.clone().into() {
            SpecialFunction::Op(operation) => ast::Infix{span: Default::default(), operation, terms: args}.into(),
            SpecialFunction::If => {
                let [condition, left, right] = args.try_into().map_err(|_| error_at!(@ "wrong number of arguments to if"))?;
                ast::IfThenElse {span: Default::default(), condition, left, right}.into()
            }
            SpecialFunction::Other(symb) => ast::Application::new_app(Default::default(),symb, args).into()
        }
    }
}

enum SpecialFunction<'a> {
    Op(Operation),
    If,
    Other(StrRef<'a>),
}

impl<'a> From<StrRef<'a>> for SpecialFunction<'a> {
    fn from(value: StrRef<'a>) -> Self {
        if value.as_str() == "if" {
            Self::If
        } else if let Some(op) = Operation::get_operation(&value) {
            Self::Op(op)
        } else {
            Self::Other(value)
        }
    }
}

/// Convertion of `squirrel` macros
///
/// `squirrel` macros don't match `cryptovampire`'s macros. As a reminder,
/// in `cryptovampire`, macros are simply meta programing for the lazy developper
/// namely, they don't reach the smt solver. However, in `squirrel`, macros have
/// some semantic. This must be translated.
///
/// # Base mapping
/// - `output` and `cond` are translated to `msg!` and `cond!` and only support
///   being applied to steps (until [this](https://gitlab.secpriv.tuwien.ac.at/secpriv/protocols/cryptovampire/-/issues/3)
///   lands that is)
/// - "general" macros are translated "as is", letting cryptovampire parser
///   error out if they are not recognise. In this category we find `input`,
///   `exec`, `frame` and a bunch of quantum stuff. The supported macros are
///   built into `cryptovampire`, those which aren't are not supported
/// - "global" macros are what `squirrel` introduces with `let`s. This
///   converniently mean we don't need to deal with `let`s anymore. These
///   macro will be declared as `cryptovampire` macros. The parser will
///   then unfold them.
///
///
/// # Global macros
///
/// Gloabl macros have a somewhat wierd behaviour regarding inputs. They remember
/// the name of the input variable and it's up to the caller to figure out by
/// `input(...)` term to replace it by.
/// Most of the logic to use them is implemented in [json::Action::prepare_term]
/// and [json::Action::convert]
pub fn convert_macro_application<'a>(
    symb: &json::path::ISymb<'a>,
    args: &[json::Term<'a>],
    timestamp: &json::Term<'a>,
    ctx: Context<'_, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    let symb = MacroNameRef(symb.path());
    match ctx.dump().get_macro(&symb) {
        Some(mmacro::Data::General(mmacro::GeneralMacro::ProtocolMacro(_))) => {
            // we use the built-in `cond` function
            apply_fun(symb.sanitized(&ctx), [timestamp], ctx)
        }
        Some(mmacro::Data::General(mmacro::GeneralMacro::Structured(_)))
        | Some(mmacro::Data::State(_)) => {
            let args = chain!(args.iter(), [timestamp]);
            apply_fun(symb.sanitized(&ctx), args, ctx)
        }
        Some(mmacro::Data::Global(g)) => {
            // we keep the input variables as input to the macro *and*
            // we keep their name
            let iargs = g.inputs().cloned().map(|var| json::Term::Var { var });

            let args: Vec<_> = chain!(
                args.iter().map(Cow::Borrowed),
                iargs.map(Cow::Owned),
                [timestamp].into_iter().map(Cow::Borrowed)
            )
            .map(|arg| arg.convert(ctx))
            .try_collect()?;
            Ok(AoOV::transpose_iter(args)).bind(|args| {
                let inner = ast::InnerAppMacro::Other {
                    name: symb.sanitized(&ctx).into(),
                    args,
                };
                trace!("{inner:}");
                Ok(AoOV::any(
                    ast::AppMacro {
                        span: Default::default(),
                        inner,
                    }
                    .into(),
                ))
            })
        }
        None => err_at!(@ "unknown macro"),
    }
}

/// Converts a `diff`.
///
/// This is the reason of all the [AoOV] monad thing. We want to extract every
/// system. Hence once we reach a diff we fork and apply the `convert` functions
/// to all possible branches. The monad makes sure everything merges properly.
/// [Context::shape] in `ctx` ensure branches that will be discarded are not
/// computed (e.g., when there is another `diff` after a first `diff`)
pub fn convert_diff<'a>(
    terms: &[json::Diff<'a>],
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let terms = terms
        .iter()
        .sorted_unstable_by_key(|x| x.proj.clone())
        .map(|x| &x.term)
        .collect_vec();
    let terms = mdo! {
        let! _ = ctx.shape().to_aoov();
        AoOV::All(terms.clone());!
    };
    let shape = terms.shape();
    mdo! {
        let! term = Ok(terms);
        term.convert(Context { shape, ..ctx });!
    }
}

/// Convert projections
///
/// For simplicity we only support tuple of size 2. This builds the inverse of
/// [convert_tuple]
pub fn convert_projection<'a>(
    id: u8,
    body: &json::Term<'a>,
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let body = body.convert(ctx);
    let unfolded = (1..id).fold(body, |acc, _| {
        mdo! {
            let! body = acc;
            pure ast::Application::new_app(Default::default(),DEFAULT_SND_PROJ_NAME, [body]).into()
        }
    });
    mdo! {
        let! unfolded = unfolded;
        pure ast::Application::new_app(Default::default(),DEFAULT_FST_PROJ_NAME, [unfolded]).into()
    }
}

pub fn convert_findst<'a>(
    vars: &[json::Term<'a>],
    condition: &json::Term<'a>,
    success: &json::Term<'a>,
    faillure: &json::Term<'a>,
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    mdo! {
        let! condition = condition.convert(ctx);
        let! success = success.convert(ctx);
        let! faillure = faillure.convert(ctx);
        let! vars = to_variable_binding(vars, ctx);
        pure FindSuchThat {
            span: Default::default(),
            vars,
            condition: condition.clone(),
            left: success.clone(),
            right: faillure.clone()
        }.into()
    }
}

pub fn convert_quantifier<'a>(
    quantificator: &json::Quant,
    vars: &[json::Term<'a>],
    body: &json::Term<'a>,
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let kind = match quantificator {
        json::Quant::ForAll => ast::QuantifierKind::Forall,
        json::Quant::Exists => ast::QuantifierKind::Exists,
        json::Quant::Seq => bail_at!(@ "seq is not a supported quantifier"),
        json::Quant::Lambda => bail_at!(@ "lambdas are not supported"),
    };
    mdo! {
        let! content = body.convert(ctx);
        let! vars = to_variable_binding(vars, ctx);
        pure ast::Quantifier {
            kind, span: Default::default(),
            vars, content: content.clone()
        }.into()
    }
}

/// Convert `squirrel` tuples
///
/// For simplicity and to avoid mutliplying axioms regarding tuples,
/// we only consider $2$-uple. $n$-uples are translated into nested $2$-uples
pub fn convert_tuple<'a>(
    elements: &[json::Term<'a>],
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let empty =
        mdo! { pure ast::Application::new_app(Default::default(),EMPTY_FUN_NAME.into(), []).into()};
    elements.iter().fold(empty, |acc, t| {
        let acc = acc?;
        let t = t.convert(ctx)?;
        mdo! {
            let! [t, acc] = Ok(AoOV::transpose_array([t, acc]));
            pure ast::Application::new_app(Default::default(),DEFAULT_TUPLE_NAME.clone(), [t, acc]).into()
        }
    })
}

pub fn convert_action_application<'a>(
    symb: &ActionName<'a>,
    args: &[json::Term<'a>],
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    apply_fun(symb.sanitized(&ctx), args, ctx)
}

/// Convert a function term to a [ast::Term] while making sure this is
/// possible in FOL. This does not always fail as `squirrel` sometime
/// give constant (e.g., `true`) as unapplied functions with no parameters
pub fn convert_function<'a>(
    symb: &OperatorName<'a>,
    ctx: Context<'_, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    if let Some(true) = ctx
        .dump()
        .get_operator(symb)
        .map(|f| f.sort.args.is_empty())
    {
        pure!(ast::Application::new_app(Default::default(), symb.sanitized(&ctx), []).into())
    } else {
        bail_at!(@ "no high order...")
    }
}
