use itertools::Either;
use std::sync::Arc;

use super::*;

use crate::{
    bail_at, err_at, error::LocationProvider, parser::{ast::extra::AsFunction, error::ParsingError, InputError, MResult, Pstr}, CVContext, CVResult, PreLocation
};

use crate::{
    container::{allocator::ContainerTools, ScopedContainer},
    formula::function::{
        inner::{
            name::Name,
            step::StepFunction,
            term_algebra::{cell::Cell, TermAlgebra},
        },
        Function, InnerFunction,
    },
    formula::sort::builtins::*,
    formula::sort::Sort,
    problem::cell::InnerMemoryCell,
    problem::step::InnerStep,
};
use utils::{string_ref::StrRef, traits::NicerError};

use super::super::ast::{self, extra::SnN, ASTList, Declaration, DeclareFunction, Ident, AST};

/// Declare the sort
pub fn declare_sorts<'str, 'bump, S>(
    env: &mut Environement<'bump, 'str, S>,
    ast: &'str ASTList<'str, S>,
) -> MResult<()>
where
    S: Pstr,
    for<'a> StrRef<'a>: From<&'a S>,
{
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(d) => match d.as_ref() {
                Declaration::Type(dt) => Some(dt),
                _ => None,
            },
            _ => None,
        })
        .try_for_each(|s| {
            let name = s.name();
            if env.sort_hash.contains_key(name.borrow()) {
                // err(merr(
                //     *s.get_name_span(),
                //     f!("the sort name {} is already in use", name),
                // ))
                Err(err_at!(
                    s.name_span(),
                    "the sort name {} is already in use",
                    name
                ))
            } else {
                let sort =
                    Sort::new_index(env.container, String::from(name.borrow()).into_boxed_str());
                let out = env.sort_hash.insert(sort.name().to_string(), sort);

                match out {
                    Some(_) => Err(err_at!(
                        s.name_span(),
                        "!UNREACHABLE!(line {} in {}) \
The sort name {} somehow reintroduced itself in the hash",
                        line!(),
                        file!(),
                        name
                    )),
                    _ => Ok(()),
                }
            }
        })
}

pub fn fetch_all<'str, 'bump, L, S>(
    env: &mut Environement<'bump, 'str, L, S>,
    ast: &'str ASTList<L, S>,
    assertions: &mut impl Extend<&'str ast::Assertion<L, S>>,
    lemmas: &mut impl Extend<&'str ast::Assertion<L, S>>,
    orders: &mut impl Extend<&'str ast::Order<L, S>>, // Vec<&'str ast::Order<'str>>,
    asserts_crypto: &mut impl Extend<&'str ast::AssertCrypto<L, S>>,
) -> CVResult<&'str ast::Assertion<L, S>, L::L>
where
    S: Pstr,
    for<'a> StrRef<'a>: From<&'a S>,
    L: PreLocation,
{
    let mut did_initilise_init = false;
    let mut query = Ok(None);
    ast.into_iter()
        .filter_map(|ast| {
            if query.is_err() {
                return None;
            };
            match ast {
                AST::Declaration(b) => match Arc::as_ref(b) {
                    Declaration::Function(fun) => Some(Either::Left(Either::Left(fun))),
                    Declaration::Cell(cell) => Some(Either::Left(Either::Right(cell))),
                    Declaration::Type(_) => None, // was done before
                },
                AST::Step(step) => Some(Either::Right(Either::Left(Arc::as_ref(step)))),
                AST::Let(mlet) => Some(Either::Right(Either::Right(Arc::as_ref(mlet)))),
                AST::Assert(a) => {
                    match Arc::as_ref(a) {
                        ast::Assert::Assertion(a) => assertions.extend([a]),
                        ast::Assert::Lemma(l) => lemmas.extend([l]),
                        ast::Assert::Query(q) => match query {
                            Err(_) => unreachable!("should be caught before"),
                            Ok(inner_query) => {
                                query = match inner_query {
                                    Some(_) => ParsingError::OneOff("only one querry is allowed")
                                        .with_location(|| q),
                                    None => Ok(Some(q)),
                                }
                            }
                        },
                    };
                    None
                }
                AST::Order(o) => {
                    orders.extend([Arc::as_ref(o)]);
                    None
                }
                AST::AssertCrypto(a) => {
                    asserts_crypto.extend([Arc::as_ref(a)]);
                    None
                }
            }
        })
        .try_for_each(|ast| match ast {
            Either::Left(Either::Left(fun)) => declare_function(env, fun).debug_continue(),
            Either::Left(Either::Right(cell)) => declare_cell(env, cell).debug_continue(),
            Either::Right(Either::Left(step)) => {
                declare_step(env, step).debug_continue()?;
                if (*step.name.name()).as_str() == "init" {
                    did_initilise_init = true;
                    if step.args().len() >= 1 {
                        return ParsingError::OneOff("the init step should have any arguments")
                            .with_location(|| &step.args);
                    }
                }
                Ok(())
            }
            Either::Right(Either::Right(mlet)) => declare_let::<S>(env, mlet),
        })?;

    if !did_initilise_init {
        declare_step(env, S::ref_init_step_ast()).map_err(|err| {
            err.set_location(ast.provide())
        })?
    }

    // query.and_then(|q| {
    //     q.ok_or(
    //         InputError::new_with_pest(pest, err)

    //         pest::error::Error::new_from_pos(
    //         pest::error::ErrorVariant::CustomError {
    //             message: "no query".to_string(),
    //         },
    //         ast.begining,
    //     ))
    // })
    query.and_then(|q| {
        q.ok_or_else(|| ParsingError::OneOff("the querry is missing"))
            .with_location(|| ast)
    })
}

fn user_bool_to_condtion<'bump>(s: Sort<'bump>) -> Sort<'bump> {
    if s == BOOL.as_sort() {
        CONDITION.clone()
    } else {
        s
    }
}

fn declare_function<'str, 'bump, L, S>(
    env: &mut Environement<'bump, 'str, L, S>,
    fun: &DeclareFunction<L, S>,
) -> CVResult<(), L::L>
where
    S: Pstr,
    for<'a> StrRef<'a>: From<&'a S>,
    L: PreLocation,
{
    let Ident {
        span,
        content: name,
    } = fun.name();
    if env.contains_name(name.borrow()) {
        // bail_at!(span, "the function name '{}' is already in use", name)
        ParsingError::already_defined("function", name.as_str()).with_location(|| fun.name())
    } else {
        let input_sorts: Result<Vec<_>, _> = fun
            .args()
            .map(|idn| get_sort(env, idn.span, idn.name().borrow()))
            .map(|s| {
                // user defined bool functions are condition
                s.map(user_bool_to_condtion)
            })
            .collect();
        let output_sort = {
            let idn = fun.out();
            get_sort(env, idn.span, idn.name().borrow())
                // user defined bool functions are condition
                .map(user_bool_to_condtion)
        }?;
        let fun = if output_sort == NAME.as_sort() {
            Function::new_from_inner(
                env.container,
                InnerFunction::Name(Name::new(name.to_string(), MESSAGE.as_sort(), input_sorts?)),
            )

            // add to env. name_caster_collection
        } else {
            Function::new_user_term_algebra(env.container, name.borrow(), input_sorts?, output_sort)
                .main
        };
        if let Some(_) = env.functions.insert(fun.name().to_string(), fun.into()) {
            unreachable!(
                "!UNREACHABLE!(line {} in {}) \
The function name {} somehow reintroduced itself in the hash",
                line!(),
                file!(),
                name
            )
        } else {
            Ok(())
        }
    }
}

fn declare_step<'str, 'bump, L, S>(
    env: &mut Environement<'bump, 'str, L, S>,
    fun: &'str ast::Step<L, S>,
) -> CVResult<(), L::L>
where
    S: Pstr,
    for<'c> StrRef<'c>: From<&'c S>,
    L: PreLocation,
{
    let SnN { span, name } = (&fun.name).into();
    if env.contains_name(&name) {
        ParsingError::already_defined("step", name.as_str()).with_location(|| &fun.name)?
    }

    let input_sorts: Result<Vec<_>, _> = fun
        .args()
        .into_iter()
        .map(|idn| get_sort(env, *idn.span, idn.name))
        .collect();
    let step = <ScopedContainer<'bump> as ContainerTools<'bump, InnerStep<'bump>>>::alloc_uninit::<
        'bump,
    >(env.container);
    let function = env
        .container
        .alloc_inner(InnerFunction::Step(StepFunction::from(step)));

    let cache = FunctionCache::Step(StepCache {
        args: input_sorts?.into(),
        args_name: fun.args_names().cloned().collect(),
        ast: fun,
        function,
        step,
    });

    let r = env.functions.insert(name.to_string(), cache);
    assert!(r.is_none());

    Ok(())
}

fn declare_cell<'str, 'bump, L, S>(
    env: &mut Environement<'bump, 'str,L,  S>,
    fun: &'str ast::DeclareCell<L,  S>,
) -> MResult<()>
where
    S: Pstr,
    for<'a> StrRef<'a>: From<&'a S>,
    L:PreLocation
{
    let SnN { span, name } = (&fun.name).into();
    if env.contains_name(&name) {
        bail_at!(span, "the cell name {} is already in use", &name)
        // return err(merr(*span, f!("the cell name {} is already in use", &name)));
    }

    let input_sorts: Result<Vec<_>, _> = fun
        .args()
        .into_iter()
        .map(|idn| get_sort(env, *idn.span, idn.name))
        .collect();
    let cell =
        <ScopedContainer<'bump> as ContainerTools<'bump, InnerMemoryCell<'bump>>>::alloc_uninit::<
            'bump,
        >(env.container);
    let function = env
        .container
        .alloc_inner(InnerFunction::TermAlgebra(TermAlgebra::Cell(Cell::new(
            cell,
        ))));

    let cache = FunctionCache::MemoryCell(CellCache {
        args: input_sorts?.into(),
        cell,
        function,
        assignements: Default::default(),
        ast: fun,
    });

    let r = env.functions.insert(name.to_string(), cache);
    assert_eq!(None, r);

    Ok(())
}

fn declare_let<'bump, 'a, S>(
    env: &mut Environement<'bump, 'a, S>,
    mlet: &ast::Macro<'a, S>,
) -> MResult<()>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    let ast::Macro { name, .. } = mlet;
    let SnN { span, name } = name.into();
    if env.container_macro_name(&name) {
        bail_at!(span, "the macro {} is already in use", &name)
    } else {
        // the input sorts (will gracefully error out later if a sort is undefined)
        let args: Result<Arc<[_]>, _> = mlet
            .args
            .into_iter()
            .map(|idn| get_sort(env, idn.span, idn.type_name.name().borrow()))
            .collect();
        let args_name = mlet.args_names().cloned().collect();

        let maco_env = Macro {
            args: args?,
            args_name,
            content: mlet.term.clone(),
        };

        let r = env.macro_hash.insert(name.to_string(), maco_env);
        assert_eq!(None, r);
        Ok(())
    }
}
