use itertools::Either;
use std::sync::Arc;

use super::*;

use crate::f;
use crate::parser::{err, merr, E};

use crate::formula::function::{
    inner::{
        step::StepFunction,
        term_algebra::{cell::Cell, name::Name, TermAlgebra},
    },
    Function, InnerFunction,
};
use crate::formula::sort::Sort;
use crate::parser::ast::extra::AsFunction;
use crate::problem::cell::InnerMemoryCell;
use crate::problem::step::InnerStep;

use crate::container::{allocator::ContainerTools, ScopedContainer};
use crate::formula::sort::builtins::*;

use super::super::ast::{self, extra::SnN, ASTList, Declaration, DeclareFunction, Ident, AST};

/// Declare the sort
pub fn declare_sorts<'a, 'bump>(
    env: &mut Environement<'bump, 'a>,
    ast: &ASTList<'a>,
) -> Result<(), E> {
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
            if env.sort_hash.contains_key(name) {
                err(merr(
                    *s.get_name_span(),
                    f!("the sort name {} is already in use", name),
                ))
            } else {
                let (sort, _) = Sort::new_user(env.container, name.to_owned().into_boxed_str());
                env.sort_hash
                    .insert(sort.name().into_string(), sort)
                    .ok_or_else(|| {
                        merr(
                            *s.get_name_span(),
                            f!(
                                "!UNREACHABLE!(line {} in {}) \
The sort name {} somehow reintroduced itself in the hash",
                                line!(),
                                file!(),
                                name
                            ),
                        )
                    })
                    .map(|_| ())
            }
        })
}

pub fn declare_fun_step_cell_let<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    ast: &'str ASTList<'str>,
) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(b) => match Box::as_ref(b) {
                Declaration::Function(fun) => Some(Either::Left(Either::Left(fun))),
                Declaration::Cell(cell) => Some(Either::Left(Either::Right(cell))),
                _ => None,
            },
            AST::Step(step) => Some(Either::Right(Either::Left(Box::as_ref(step)))),
            AST::Let(mlet) => Some(Either::Right(Either::Right(Box::as_ref(mlet)))),
            _ => None,
        })
        .try_for_each(|ast| match ast {
            Either::Left(Either::Left(fun)) => declare_function(env, fun),
            Either::Left(Either::Right(cell)) => declare_cell(env, cell),
            Either::Right(Either::Left(step)) => declare_step(env, step),
            Either::Right(Either::Right(mlet)) => declare_let(env, mlet),
        })
}

fn declare_function<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    fun: &DeclareFunction<'str>,
) -> Result<(), E> {
    let Ident {
        span,
        content: name,
    } = fun.name();
    if env.contains_name(name) {
        err(merr(
            span,
            f!("the function name {} is already in use", name),
        ))
    } else {
        let input_sorts: Result<Vec<_>, _> = fun
            .args()
            .map(|idn| get_sort(env, idn.span, idn.content))
            .collect();
        let output_sort = {
            let idn = fun.out();
            get_sort(env, idn.span, idn.content)
        }?;
        let fun = if output_sort == NAME.as_sort() {
            Function::new_from_inner(
                env.container,
                InnerFunction::TermAlgebra(TermAlgebra::Name(Name::new(
                    name.to_string(),
                    MESSAGE.as_sort(),
                    input_sorts?,
                ))),
            )

            // add to env. name_caster_collection
        } else {
            Function::new_user_term_algebra(env.container, name, input_sorts?, output_sort).main
        };
        if let Some(_) = env.functions.insert(fun.name().to_string(), fun.into()) {
            err(merr(
                span,
                f!(
                    "!UNREACHABLE!(line {} in {}) \
The function name {} somehow reintroduced itself in the hash",
                    line!(),
                    file!(),
                    name
                ),
            ))
        } else {
            Ok(())
        }
    }
}

fn declare_step<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    fun: &'str ast::Step<'str>,
) -> Result<(), E> {
    let SnN { span, name } = fun.name();
    if env.contains_name(&name) {
        return err(merr(*span, f!("the step name {} is already in use", &name)));
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
        args_name: fun.args_names().collect(),
        ast: fun,
        function,
        step,
    });

    let r = env.functions.insert(name.to_string(), cache);
    assert_eq!(None, r);

    Ok(())
}

fn declare_cell<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    fun: &'str ast::DeclareCell<'str>,
) -> Result<(), E> {
    let SnN { span, name } = fun.name();
    if env.contains_name(&name) {
        return err(merr(*span, f!("the cell name {} is already in use", &name)));
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
        ast: fun
    });

    let r = env.functions.insert(name.to_string(), cache);
    assert_eq!(None, r);

    Ok(())
}

fn declare_let<'bump, 'a>(
    env: &mut Environement<'bump, 'a>,
    mlet: &ast::Macro<'a>,
) -> Result<(), E> {
    let ast::Macro { name, .. } = mlet;
    let SnN { span, name } = name.into();
    if env.container_macro_name(&name) {
        err(merr(*span, f!("the macro {}! is already in use", name)))
    } else {
        // the input sorts (will gracefully error out later if a sort is undefined)
        let args: Result<Arc<[_]>, _> = mlet
            .args()
            .into_iter()
            .map(|idn| get_sort(env, *idn.span, idn.name))
            .collect();
        let args_name = mlet.args_names().collect();

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
