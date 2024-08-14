mod ast_convertion {

    // FIXME: do it better
    const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static("_$tuple");
    const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$fst");
    const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$snd");

    use cryptovampire_lib::formula::{
        function::builtin::EMPTY_FUN_NAME,
        sort::builtins::{BOOL, MESSAGE, STEP},
    };
    use if_chain::if_chain;
    use itertools::Itertools;
    use utils::{
        all_or_one::{AllOrOneShape, AoOV},
        mdo,
        string_ref::StrRef,
    };

    use crate::{
        bail_at, err_at,
        parser::{
            ast::{self, FindSuchThat},
            FromStaticString, InputError,
        },
        squirrel::json::{self, Named, Pathed, ProcessedSquirrelDump},
    };

    use utils::monad::Monad;

    type RAoO<T> = Result<AoOV<T>, InputError>;

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Context<'a, 'str> {
        shape: AllOrOneShape,
        dump: &'a ProcessedSquirrelDump<'str>,
    }

    pub trait ToAst<'a> {
        type Target;

        fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target>;
    }

    impl<'a> ToAst<'a> for json::Term<'a> {
        type Target = ast::Term<'a, StrRef<'a>>;

        fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
            match self {
                json::Term::Fun { .. }
                | json::Term::Name { .. }
                | json::Term::Macro { .. }
                | json::Term::Action { .. } => bail_at!(@ "no high order"),
                json::Term::Let { .. } => bail_at!(@ "no lets"),
                // actual work
                json::Term::Var { var } => {
                    mdo!(pure ast::Application::from(var.name().drop_guard()).into())
                }
                json::Term::Tuple { elements } => {
                    let empty =
                        mdo! { pure ast::Application::new_app(EMPTY_FUN_NAME.into(), []).into()};

                    elements.into_iter().fold(empty, |acc, t| {
                            let acc = acc?;
                            let t = t.convert(ctx)?;
                            mdo!{
                                let! [t, acc] = Ok(AoOV::transpose_array([t, acc]));
                                pure ast::Application::new_app(DEFAULT_TUPLE_NAME.clone(), [t, acc]).into()
                            }
                    })
                }
                json::Term::Quant {
                    quantificator,
                    vars,
                    body,
                } => {
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
                            vars: vars.into_iter().collect(), content: content.clone()
                        }.into()
                    }

                    // ast::Quantifier
                    // todo!()
                }
                json::Term::Find {
                    vars,
                    condition,
                    success,
                    faillure,
                } => mdo! {
                    let! condition = condition.convert(ctx);
                    let! success = success.convert(ctx);
                    let! faillure = faillure.convert(ctx);
                    let! vars = to_variable_binding(vars, ctx);
                    pure FindSuchThat {
                        span: Default::default(),
                        vars: vars.into_iter().collect(),
                        condition: condition.clone(),
                        left: success.clone(),
                        right: faillure.clone()
                    }.into()
                },
                json::Term::Proj { id, body } => {
                    let body = body.convert(ctx);
                    let unfolded = (1..*id).fold(body, |acc, _| {
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
                json::Term::Diff { terms } => {
                    let terms = terms
                        .iter()
                        .sorted_unstable_by_key(|x| x.proj.clone())
                        .map(|x| &x.term)
                        .collect_vec();

                    let terms = mdo! {
                        let! _ = ctx.shape.to_aoov();
                        AoOV::All(terms.clone());!
                    };
                    let shape = terms.shape();

                    mdo! {
                        let! term = Ok(terms);
                        term.convert(Context { shape, ..ctx });!
                    }
                }
                json::Term::App { f, args } => match f.as_ref() {
                    json::Term::Fun { symb } => {
                        let args: Vec<_> = if_chain! {
                            if let Some(f) = ctx.dump.get_operator(symb);
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
                            let! args = Ok(AoOV::transpose(args));
                            pure ast::Application::new_app(symb.equiv_name_ref(), args).into()
                        }
                    }
                    _ => Err(err_at!(@ "no high order")),
                },
            }
        }
    }

    fn to_variable_binding<'a, 'b>(
        vars: &[json::Term<'a>],
        ctx: Context<'b, 'a>,
    ) -> RAoO<Vec<(StrRef<'a>, ast::TypeName<'a, StrRef<'a>>)>> {
        let mut res = Ok(());

        let iter = vars
            .iter()
            .map(|t| match t {
                json::Term::Var { var } => Ok(var),
                _ => Err(err_at!(@ "not a variable")),
            })
            .map(|x| {
                x.and_then(|var| {
                    mdo! {
                        let! sort = var.sort.convert(ctx);
                        pure (var.id.name().drop_guard(), sort)
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

        let out = AoOV::transpose(iter);
        res.map(|_| out)
    }
    // ()

    impl<'a> ToAst<'a> for json::sort::Type<'a> {
        type Target = ast::TypeName<'a, StrRef<'a>>;

        fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
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
}
