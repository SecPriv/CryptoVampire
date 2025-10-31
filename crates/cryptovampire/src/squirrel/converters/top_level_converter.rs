use std::sync::Arc;

use ast::StrApplicable;
use convert_order::mk_depends_mutex_lemmas;
use log::{info, trace};

use super::{Context, *};
use crate::ast_forall;
use crate::squirrel::Sanitizable;

pub fn convert_squirrel_dump(dump: SquirrelDump<'_>) -> RAoO<ast::ASTList<'_, StrRef<'_>>> {
    let pdump = &ProcessedSquirrelDump::from(dump);

    let ctx = ContextBuilder::create_empty().dump(pdump).build().unwrap();

    let types = mk_types(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Type(d)))));

    let funs = mk_funs_and_names(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Function(d)))));

    let cells = mk_cells(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Cell(d)))));

    let macros = mk_macros(pdump, ctx).map(|r| r.mmap(|d| ast::AST::Let(Arc::new(d))));

    let steps = mk_steps(pdump, ctx).map(|r| r.mmap(|d| ast::AST::Step(Arc::new(d))));

    let assertions = mk_assertions()
        .map(Arc::new)
        .map(ast::AST::Assert)
        .map(RAoO::pure);

    let assert_crypto = assert_crypto(pdump, ctx).map(RAoO::pure);

    let order = {
        mk_depends_mutex_lemmas(pdump.actions(), ctx).map(|o| {
            mdo! {
                let! order = o;
                pure ast::AST::Order(Arc::new(order))
            }
        })
    };

    let query = mk_query(pdump, ctx).mmap(|content| {
        ast::AST::Assert(Arc::new(ast::Assert::Query(ast::Assertion {
            span: Default::default(),
            content,
            options: Default::default(),
        })))
    });

    // TODO:
    // - [x] add builtin functions
    // - [x] convert known function (e.g. && => and)
    // - [x] declare names
    // - [-] make init step; possibly not needed
    // - [x] assert tuples
    // - [x] assert crypto
    // - [x] ordering
    // - [ ] <> (i.e., !=); maybe using infix

    let all: Vec<_> = chain!(
        types,
        cells,
        funs,
        macros,
        assertions,
        steps,
        order,
        assert_crypto,
        [query]
    )
    .map(|x| {
        if cfg!(debug_assertions) {
            mdo! {
                let! x = x;
                pure {
                    trace!("converted:\n\t{x}");
                    x
                }
            }
        } else {
            x
        }
    })
    .try_collect()?;
    mdo! {
      let! content = Ok(AoOV::transpose_iter(all));
      pure ast::ASTList {content, location: Default::default()}
    }
}

/// Make basic assertions
fn mk_assertions<'a>() -> [ast::Assert<'a, StrRef<'a>>; 2] {
    [
        ast_forall!(x:"Message",y:"Message"; {
            "==".app([DEFAULT_FST_PROJ_NAME.app([DEFAULT_TUPLE_NAME.app([x.clone(), y.clone()])]), x.into()])
        }),
        ast_forall!(x:"Message",y:"Message"; {
            "==".app([DEFAULT_SND_PROJ_NAME.app([DEFAULT_TUPLE_NAME.app([x.clone(), y.clone()])]), y.into()])
        }),
    ]
    .map(|x| ast::Assertion {
        span: Default::default(),
        content: x,
        options: Default::default(),
    })
    .map(ast::Assert::Assertion)
}

use assert_crypto::assert_crypto;
mod assert_crypto {
    use itertools::Either;
    use json::operator::OperatorName;

    use super::*;
    use crate::formula::sort::builtins::{BOOL, MESSAGE};
    use crate::squirrel::{FakeSanitizable, SanitizeKind};

    pub fn assert_crypto<'a, 'b>(
        pdump: &'b ProcessedSquirrelDump<'a>,
        ctx: Context<'b, 'a>,
    ) -> impl Iterator<Item = ast::AST<'a, StrRef<'a>>> + 'b {
        chain!(
            ["nonce", "memory_cell", "unfolding"].map(|s| {
                ast::AST::AssertCrypto(Arc::new(ast::AssertCrypto {
                    span: Default::default(),
                    name: StrRef::from(s).into(),
                    functions: vec![],
                    options: Default::default(),
                }))
            }),
            pdump
                .operators_with_symb()
                .filter_map(move |(symb, f)| {
                    use json::operator::{AbstractDef, Def};
                    match f.def() {
                        Def::Concrete(_) => None,
                        Def::Abstract {
                            abstract_def,
                            associated_fun,
                        } => match abstract_def {
                            AbstractDef::Hash => {
                                Some(Either::Left(assert_euf(ctx, symb, None, None)))
                            }
                            AbstractDef::SEnc => {
                                let sdec = associated_fun
                                    .first()
                                    .expect("missing associated function in sdec");
                                Some(Either::Right(
                                    [assert_int_ctxt(ctx, symb, sdec)].into_iter(),
                                ))
                            }
                            AbstractDef::CheckSign => {
                                let mut iter = associated_fun.iter();
                                let sign =
                                    iter.next().expect("missing associated function in sign");
                                let vk = iter.next();
                                Some(Either::Left(assert_euf(ctx, sign, Some(symb), vk)))
                            }
                            _ => None,
                        },
                    }
                })
                .flatten()
        )
    }

    fn assert_euf<'a, 'b>(
        ctx: Context<'b, 'a>,
        hash: &OperatorName<'a>,
        verify: Option<&OperatorName<'a>>,
        vk: Option<&OperatorName<'a>>,
    ) -> impl Iterator<Item = ast::AST<'a, StrRef<'a>>> + 'b {
        let mut new_fun = None;
        let is_hmac = verify.is_none();
        let verify = if let Some(verify) = verify {
            ast::Function::from_name(verify.sanitized(&ctx))
        } else {
            // declare a dummy verify
            let name: StrRef<'static> = format!("verify_{}", hash.sanitized(&ctx)).into();
            new_fun = Some(ast::DeclareFunction::new(
                Default::default(),
                name.clone(),
                std::iter::repeat(MESSAGE.name()).take(3),
                BOOL.name(),
            ));
            ast::Function::from_name(name)
        };
        let vk = vk.map(|vk| ast::Function::from_name(vk.sanitized(&ctx)));
        let hash = ast::Function::from_name(hash.sanitized(&ctx));
        let options = if is_hmac {
            assert!(vk.is_none());
            [StrRef::from("hmac")].into_iter().collect()
        } else {
            Default::default()
        };
        chain!(
            [ast::AssertCrypto {
                span: Default::default(),
                name: StrRef::from("euf-cma").into(),
                functions: chain!([hash, verify], vk).collect(),
                options,
            }]
            .map(Arc::new)
            .map(ast::AST::AssertCrypto),
            new_fun.map(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Function(d))))
        )
    }

    fn assert_int_ctxt<'a>(
        ctx: Context<'_, 'a>,
        senc: &OperatorName<'a>,
        sdec: &OperatorName<'a>,
    ) -> ast::AST<'a, StrRef<'a>> {
        let funs = [senc, sdec].map(|f| ast::Function::from_name(f.sanitized(&ctx)));
        let fail = ast::Function::from_name(
            FakeSanitizable {
                str: DEFAULT_FAIL_NAME,
                kind: SanitizeKind::Function,
            }
            .sanitized(&ctx),
        );
        ast::AST::AssertCrypto(Arc::new(ast::AssertCrypto {
            span: Default::default(),
            name: StrRef::from("int_ctxt").into(),
            functions: chain!(funs, [fail]).collect(),
            options: Default::default(),
        }))
    }
}

fn mk_steps<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::Step<'a, StrRef<'a>>>> + 'b {
    pdump
        .actions()
        .debug("attempting to convert step:\n\t")
        .map(move |a| a.convert(ctx))
}

fn mk_query<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> RAoO<ast::Term<'a, StrRef<'a>>> {
    {
        let quantificator = json::Quant::ForAll;
        let vars = pdump
            .variables()
            .iter()
            .cloned()
            .map(|var| json::Term::Var { var })
            .collect();
        let hypothese = pdump.hypotheses().iter().cloned().fold(
            json::Term::mk_app(StrRef::new_borrowed("true").unwrap(), []),
            |acc, t| json::Term::mk_app(StrRef::new_borrowed("&&").unwrap(), [acc, t]),
        );

        let body = Box::new(json::Term::mk_app(
            StrRef::new_borrowed("=>").unwrap(),
            [hypothese, pdump.query().clone()],
        ));

        json::Term::Quant {
            quantificator,
            vars,
            body,
        }
    }
    .convert(ctx)
}

fn mk_cells<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::DeclareCell<'a, StrRef<'a>>>> + 'b {
    pdump
        .macros_with_symb()
        .filter_map(|(symb, data)| match data {
            json::mmacro::Data::State(json::mmacro::StateMacro {
                sort,
                init: json::mmacro::StateMacroDef { vars, .. },
                ..
            }) => Some((symb, sort, vars)),
            _ => None,
        })
        .map(move |(symb, sort, vars)| {
            mdo! {
                let! sort = sort.convert(ctx);
                let args : Vec<_> = vars.iter().map(|v| v.sort().convert(ctx)).try_collect()?;
                let! args = Ok(AoOV::transpose_iter(args));
                pure ast::DeclareCell::new(Default::default(),symb.sanitized(&ctx), args, sort.clone())
            }
        })
}

fn mk_macros<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::Macro<'a, StrRef<'a>>>> + 'b {
    let base = pdump
        .macros_with_symb()
        .map_into()
        .map(move |m: MacroRef<'a, 'b>| m.convert(ctx))
        .filter_map(helper_functions::transpose_raov);
    let concrete_functions = pdump
        .operators_with_symb()
        .filter_map(|(symb, json::operator::Data { def, .. })| def.as_concrete().map(|c| (symb, c)))
        .map(move |(symb, json::operator::Concrete { args, body, .. })| {
            ConcreteMacro {
                symb: symb.as_ref(),
                body,
                args: args.as_slice().into(),
            }
            .convert(ctx)
        });
    chain!(base, concrete_functions)
}

fn mk_funs_and_names<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::DeclareFunction<'a, StrRef<'a>>>> + 'b {
    let names = pdump
        .names_with_symb()
        .debug("attempting to convert name:\n\t")
        .map(move |(symb, json::FunctionType { vars, args, .. })| {
            (symb.sanitized(&ctx), vars, args, &json::Type::Name)
        });

    let functions = pdump
        .operators_with_symb()
        .debug("attempting to convert function:\n\t")
        .filter_map(move |(symb, data)| {
            // filtering out builtin and forbidden functions
            let symb_str_ref = symb.to_str_ref();
            (!(ctx.forbidden_function().contains(symb_str_ref.as_ref())
                || ctx.builtin_function().contains(symb_str_ref.as_ref())))
            .then(|| (symb.sanitized(&ctx), data))
        })
        .filter_map(
            |(
                symb,
                json::operator::Data {
                    sort: json::FunctionType { vars, args, out },
                    def,
                },
            )| { (!def.is_concrete()).then_some((symb, vars, args, out)) },
        );

    chain!(names, functions)
        .filter(|(symb, vars, _, _)| {
            if cfg!(debug_assertions) && !vars.is_empty() {
                info!("skipping {symb} because of polymorphism");
            };
            vars.is_empty()
        })
        .map(move |(symb, vars, args, out)| {
            trace!("converting {symb}...");
            if !vars.is_empty() {
                bail_at!(@ "polymorphism...")
            }
            out.convert(ctx).bind(|sort| {
                trace!("converting {symb} with sort {sort}");
                // let args: Vec<_> = args.iter().map(|arg| arg.convert(ctx)).try_collect()?;
                let args: Vec<_> = {
                    let args = match args.last() {
                        Some(json::Type::Tuple { elements }) => elements,
                        _ => args,
                    };
                    args.iter().map(|arg| arg.convert(ctx)).try_collect()
                }?;
                mdo! {
                    let! args = Ok(AoOV::transpose_iter(args));
                    pure ast::DeclareFunction::new(Default::default(),symb.clone(), args, sort.clone())
                }
            })
        })
}

fn mk_types<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::DeclareType<'a, StrRef<'a>>>> + 'b {
    pdump
        .types_with_symb()
        .filter_map(move |(symb, data)| {
            if data.can_be_index() {
                Some(ast::DeclareType::new(symb.sanitized(&ctx).into()))
            } else {
                None
            }
        })
        .chain([ast::DeclareType::new(
            StrRef::from_static(INDEX_SORT_NAME).into(),
        )])
        .map(Monad::pure)
}
