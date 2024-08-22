use cryptovampire_lib::formula::function::builtin::EMPTY_FUN_NAME;
use if_chain::if_chain;
use itertools::{chain, Itertools};
use utils::{all_or_one::AoOV, mdo, pure, string_ref::StrRef};

use crate::{
    bail_at, err_at,
    parser::ast::{self, FindSuchThat, Term},
    squirrel::{
        converters::{
            ast_convertion::ToAst, helper_functions::to_variable_binding, DEFAULT_FST_PROJ_NAME,
            DEFAULT_SND_PROJ_NAME, DEFAULT_TUPLE_NAME,
        },
        json::{self, mmacro, path::Path, Pathed},
    },
};

use utils::monad::Monad;

use super::{
    super::{Context, RAoO},
    apply_fun,
};

pub fn convert_application<'a, 'b>(
    f: &json::Term<'a>,
    args: &Vec<json::Term<'a>>,
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    match f {
        json::Term::Fun { symb } => convert_function_application(symb, args, ctx),
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
        | json::Term::Quant { .. } => Err(err_at!(@ "no high order")),
    }
}

/// Convert the application of a name
pub fn convert_name_application<'a, 'b>(
    symb: &json::path::ISymb<'a>,
    args: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    apply_fun(symb.equiv_name_ref(&ctx), args, ctx)
}

/// Convert the application of a function.
///
/// The trickiest point of the functio is to take care of functions that take
/// tuples as arguments. There is a discrepency between `squirrel` and `cryptovampire`
/// with that regard. `squirrel` uses tuples to avoid partial application of certain
/// cryptographic function (e.g., `enc`); there is no such problem in `cryptovampire`
/// so such a work around was never implemented, and I'm not planning to implement one.
fn convert_function_application<'a, 'b>(
    symb: &json::path::Path<'a>,
    args: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    let args: Vec<_> = if_chain! {
        if let Some(f) = ctx.dump().get_operator(symb);
        let args_type = f.sort.args.as_slice();
        if args_type.len() == 1;
        if let Some(json::sort::Type::Tuple {..}) = args_type.first();
        if let Some(json::Term::Tuple { elements }) = args.first();
        then { elements } // If it uses tuples as argument, we collapse it
        else { args }
    }
    .iter()
    .map(|arg| arg.convert(ctx))
    .try_collect()?;
    mdo! {
        let! args = Ok(AoOV::transpose_iter(args));
        pure ast::Application::new_app(symb.equiv_name_ref(&ctx), args).into()
    }
}

/// Convertion of `squirrel` macros
///
/// `squirrel` macros don't match `cryptovampire`'s macros. As a reminder,
/// in `cryptovampire`, macros are simply meta programing for the lazy developper
/// namely, they don't reach the smt solver. However, in `squirrel`, macros have
/// some semantic. This must be translated.
///
/// Thus:
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
pub fn convert_macro_application<'a, 'b>(
    symb: &json::path::ISymb<'a>,
    args: &[json::Term<'a>],
    timestamp: &json::Term<'a>,
    ctx: Context<'b, 'a>,
) -> RAoO<Term<'a, StrRef<'a>>> {
    let symb = symb.s_symb.as_ref();
    let args = chain!(args.iter(), [timestamp]);
    match ctx.dump().get_macro(symb) {
        Some(mmacro::Data::General(mmacro::GeneralMacro::ProtocolMacro(p))) => {
            timestamp.convert(ctx).bind(|t| match &t.inner {
                ast::InnerTerm::Application(app) => {
                    let inner = match p {
                        mmacro::ProtocolMacro::Output => ast::InnerAppMacro::Msg((**app).clone()),
                        mmacro::ProtocolMacro::Cond => ast::InnerAppMacro::Cond((**app).clone()),
                    };
                    Ok(AoOV::any(
                        ast::AppMacro {
                            span: Default::default(),
                            inner,
                        }
                        .into(),
                    ))
                }
                _ => {
                    let msg = "output/cond/msg macro are only supported \
                                    when applied to a concrete timepoint";
                    Err(err_at!(@ "{msg}"))
                }
            })
        }
        Some(mmacro::Data::General(mmacro::GeneralMacro::Structured(_)))
        | Some(mmacro::Data::State(_)) => apply_fun(symb.equiv_name_ref(&ctx), args, ctx),
        Some(mmacro::Data::Global(_)) => {
            let args: Vec<_> = args.map(|arg| arg.convert(ctx)).try_collect()?;
            Ok(AoOV::transpose_iter(args)).bind(|args| {
                let inner = ast::InnerAppMacro::Other {
                    name: symb.equiv_name_ref(&ctx).into(),
                    args,
                };
                Ok(AoOV::any(
                    ast::AppMacro {
                        span: Default::default(),
                        inner,
                    }
                    .into(),
                ))
            })
        }
        None => Err(err_at!(@ "unknown macro")),
    }
}

/// Converts a `diff`.
///
/// This is the reason of all the [AoOV] monad thing. We want to extract every
/// system. Hence once we reach a diff we fork and apply the `convert` functions
/// to all possible branches. The monad makes sure everything merges properly.
/// [Context::shape] in `ctx` ensure branches that will be discarded are not
/// computed (e.g., when there is another `diff` after a first `diff`)
pub fn convert_diff<'a, 'b>(
    terms: &[json::Diff<'a>],
    ctx: Context<'b, 'a>,
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
pub fn convert_projection<'a, 'b>(
    id: u8,
    body: &json::Term<'a>,
    ctx: Context<'b, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let body = body.convert(ctx);
    let unfolded = (1..id).fold(body, |acc, _| {
        mdo! {
            let! body = acc;
            pure ast::Application::new_app(DEFAULT_SND_PROJ_NAME, [body]).into()
        }
    });
    mdo! {
        let! unfolded = unfolded;
        pure ast::Application::new_app(DEFAULT_FST_PROJ_NAME, [unfolded]).into()
    }
}

pub fn convert_findst<'a, 'b>(
    vars: &[json::Term<'a>],
    condition: &json::Term<'a>,
    success: &json::Term<'a>,
    faillure: &json::Term<'a>,
    ctx: Context<'b, 'a>,
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

pub fn convert_quantifier<'a, 'b>(
    quantificator: &json::Quant,
    vars: &[json::Term<'a>],
    body: &json::Term<'a>,
    ctx: Context<'b, 'a>,
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
pub fn convert_tuple<'a, 'b>(
    elements: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    let empty = mdo! { pure ast::Application::new_app(EMPTY_FUN_NAME.into(), []).into()};
    elements.into_iter().fold(empty, |acc, t| {
        let acc = acc?;
        let t = t.convert(ctx)?;
        mdo! {
            let! [t, acc] = Ok(AoOV::transpose_array([t, acc]));
            pure ast::Application::new_app(DEFAULT_TUPLE_NAME.clone(), [t, acc]).into()
        }
    })
}

pub fn convert_action_application<'a, 'b>(
    symb: &json::path::Path<'a>,
    args: &[json::Term<'a>],
    ctx: Context<'b, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    apply_fun(symb.equiv_name_ref(&ctx), args, ctx)
}

/// Convert a function term to a [ast::Term] while making sure this is
/// possible in FOL. This does not always fail as `squirrel` sometime
/// give constant (e.g., `true`) as unapplied functions with no parameters
pub fn convert_function<'a, 'b>(
    symb: &Path<'a>,
    ctx: Context<'b, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    if let Some(true) = ctx
        .dump()
        .get_operator(symb)
        .map(|f| f.sort.args.is_empty())
    {
        pure!(ast::Application::new_app(symb.equiv_name_ref(&ctx), []).into())
    } else {
        bail_at!(@ "no high order...")
    }
}
