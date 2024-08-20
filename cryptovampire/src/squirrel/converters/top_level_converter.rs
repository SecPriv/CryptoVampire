use std::sync::Arc;

use super::*;

pub fn convert_squirrel_dump<'a>(dump: SquirrelDump<'a>) -> RAoO<ast::ASTList<'a, StrRef<'a>>> {
    let pdump = &ProcessedSquirrelDump::from(dump);

    let ctx = ast_convertion::Context::new(pdump);

    let types = mk_types(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Type(d)))));

    let funs = mk_funs(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Function(d)))));

    let cells = mk_cells(pdump, ctx)
        .map(|r| r.mmap(|d| ast::AST::Declaration(Arc::new(ast::Declaration::Cell(d)))));

    let macros = mk_macros(pdump, ctx).map(|r| r.mmap(|d| ast::AST::Let(Arc::new(d))));

    let steps = mk_steps(pdump, ctx).map(|r| r.mmap(|d| ast::AST::Step(Arc::new(d))));

    let query = mk_query(pdump, ctx).mmap(|content| {
        ast::AST::Assert(Arc::new(ast::Assert::Query(ast::Assertion {
            span: Default::default(),
            content,
            options: Default::default(),
        })))
    });

    /* TODO:
        - add builtin functions
        - make init step
        - convert known function (e.g. && => and)
        - assert tuples
        - assert crypto
    */

    let all: Vec<_> = chain!([query], types, cells, macros, steps, funs).try_collect()?;
    mdo! {
      let! content = Ok(AoOV::transpose_iter(all));
      pure ast::ASTList {content, begining: None}
    }
}

fn mk_steps<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::Step<'a, StrRef<'a>>>> + 'b {
    pdump.actions().values().map(move |a| a.convert(ctx))
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
        .macros()
        .iter()
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
                pure ast::DeclareCell::new(symb.equiv_name_ref(), args, sort.clone())
            }
        })
}

fn mk_macros<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::Macro<'a, StrRef<'a>>>> + 'b {
    let base = pdump
        .macros()
        .iter()
        .map_into()
        .map(move |m: MacroRef| m.convert(ctx))
        .filter_map(helper_functions::transpose_raov);
    let concrete_functions = pdump
        .operators()
        .iter()
        .filter_map(|(symb, json::operator::Data { def, .. })| def.as_concrete().map(|c| (symb, c)))
        .map(move |(symb, json::operator::Concrete { args, body, .. })| {
            ConcreteMacro {
                symb,
                body,
                args: args.as_slice().into(),
            }
            .convert(ctx)
        });
    chain!(base, concrete_functions)
}

fn mk_funs<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::DeclareFunction<'a, StrRef<'a>>>> + 'b {
    pdump
        .operators()
        .iter()
        .filter_map(
            |(
                symb,
                json::operator::Data {
                    sort: json::FunctionType { vars, args, out },
                    def,
                },
            )| { (!def.is_concrete()).then_some((symb, vars, args, out)) },
        )
        .map(move |(symb, vars, args, out)| {
            if !vars.is_empty() {
                bail_at!(@ "polymorphism...")
            }
            mdo! {
                let! sort = out.convert(ctx);
                let args : Vec<_> = args.iter().map(|arg| arg.convert(ctx)).try_collect()?;
                let! args = Ok(AoOV::transpose_iter(args));
                pure ast::DeclareFunction::new(symb.equiv_name_ref(), args, sort.clone())
            }
        })
}

fn mk_types<'a, 'b>(
    pdump: &'b ProcessedSquirrelDump<'a>,
    _: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::DeclareType<'a, StrRef<'a>>>> + 'b {
    pdump
        .types()
        .iter()
        .filter_map(|(symb, data)| {
            if data.can_be_index() {
                Some(ast::DeclareType::new(symb.equiv_name_ref().into()))
            } else {
                None
            }
        })
        .chain([ast::DeclareType::new(
            StrRef::from_static(INDEX_SORT_NAME).into(),
        )])
        .map(Monad::pure)
}
