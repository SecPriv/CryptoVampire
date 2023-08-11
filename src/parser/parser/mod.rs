use itertools::Either;

use self::parsing_environement::{get_sort, Environement, FunctionCache};

use super::{
    ast::{
        extra::{self, AsFunction, SnN},
        ASTList, Declaration, DeclareFunction, Ident, AST,
    },
    *,
};
use crate::{
    container::{
        allocator::{Container, ContainerTools},
        ScopedContainer,
    },
    formula::{
        function::{
            inner::{
                step::StepFunction,
                term_algebra::{cell::Cell, name::Name, TermAlgebra},
            },
            Function, InnerFunction,
        },
        sort::{
            builtins::{MESSAGE, NAME},
            Sort,
        },
    },
    problem::{cell::InnerMemoryCell, step::InnerStep},
};

pub mod guard;
pub mod parsable_trait;
pub mod parsing_environement;
pub mod state;

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
    fun: &ast::Step<'str>,
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

    let cache = FunctionCache::Step {
        args: input_sorts?.into(),
        args_name: fun.args_names().collect(),
        ast: Box::new(fun.clone()),
        function,
        step,
    };

    let r = env.functions.insert(name.to_string(), cache);
    assert_eq!(None, r);

    Ok(())
}

fn declare_cell<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    fun: &ast::DeclareCell<'str>,
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

    let cache = FunctionCache::MemoryCell {
        args: input_sorts?.into(),
        cell,
        function,
        assignements: Default::default(),
    };

    let r = env.functions.insert(name.to_string(), cache);
    assert_eq!(None, r);

    Ok(())
}

pub fn declare_fun_step_cell<'str, 'bump>(
    env: &mut Environement<'bump, 'str>,
    ast: &ASTList<'str>,
) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Declaration(b) => match Box::as_ref(b) {
                Declaration::Function(fun) => Some(Either::Left(Either::Left(fun))),
                Declaration::Cell(cell) => Some(Either::Left(Either::Right(cell))),
                _ => None,
            },
            AST::Step(step) => Some(Either::Right(Box::as_ref(step))),
            _ => None,
        })
        .try_for_each(|ast| match ast {
            Either::Left(Either::Left(fun)) => declare_function(env, fun),
            Either::Left(Either::Right(cell)) => declare_cell(env, cell),
            Either::Right(step) => declare_step(env, step),
        })
}


fn declare_let<'bump, 'a>(env: &mut Environement<'bump, 'a>, ast: &ASTList<'a>) -> Result<(), E> {
    ast.into_iter()
        .filter_map(|ast| match ast {
            AST::Let(b) => Some(b.as_ref()),
            _ => None,
        })
        .try_for_each(|mlet| {
            let super::ast::Macro { name, .. } = mlet;
            let SnN { span, name } = name.into();
            // TODO: no hard-coded values
            if env.macro_hash.contains_key(name.as_ref())
                || ["msg", "cond"].contains(&name.as_ref())
            {
                err(merr(*span, f!("the macro {}! is already in use", name)))
            } else {
                // the input sorts (will gracefully error out later if a sort is undefined)
                let _input_sorts: Result<Vec<_>, _> = mlet
                    .args()
                    .into_iter()
                    .map(|idn| get_sort(env, *idn.span, idn.name))
                    .collect();

                todo!()
            }
        })
}

// /// declare the user function (e.g., tuple & co)
// pub fn declare_functions<'a, 'bump>(
//     env: &mut Environement<'bump, 'a>,
//     ast: &ASTList<'a>,
// ) -> Result<(), E> {
//     ast.into_iter()
//         .filter_map(|ast| match ast {
//             AST::Declaration(b) => match b.as_ref() {
//                 Declaration::Function(f) => Some(f),
//                 _ => None,
//             },
//             _ => None,
//         })
//         .try_for_each(|fun| {
//             let Ident {
//                 span,
//                 content: name,
//             } = fun.name();
//             if env.function_hash.contains_key(name) {
//                 err(merr(
//                     span,
//                     f!("the function name {} is already in use", name),
//                 ))
//             } else {
//                 let input_sorts: Result<Vec<_>, _> = fun
//                     .args()
//                     .map(|idn| get_sort(env, idn.span, idn.content))
//                     .collect();
//                 let output_sort = {
//                     let idn = fun.out();
//                     get_sort(env, idn.span, idn.content)
//                 }?;
//                 let fun = if output_sort == NAME.as_sort() {
//                     Function::new_from_inner(
//                         env.container,
//                         InnerFunction::TermAlgebra(TermAlgebra::Name(Name::new(
//                             name.to_string(),
//                             MESSAGE.as_sort(),
//                             input_sorts?,
//                         ))),
//                     )

//                     // add to env. name_caster_collection
//                 } else {
//                     Function::new_user_term_algebra(env.container, name, input_sorts?, output_sort)
//                         .main
//                 };
//                 if let Some(_) = env.function_hash.insert(fun.name().to_string(), fun) {
//                     err(merr(
//                         span,
//                         f!(
//                             "!UNREACHABLE!(line {} in {}) \
// The function name {} somehow reintroduced itself in the hash",
//                             line!(),
//                             file!(),
//                             name
//                         ),
//                     ))
//                 } else {
//                     Ok(())
//                 }
//             }
//         })
// }

// /// Declare memory cells and steps.
// ///
// /// The functions are also added to the list of things to initialize as the
// /// they are kept empty. For instance a step might depend on itself.
// pub fn declare_steps_and_cells<'a, 'bump>(
//     env: &mut Environement<'bump, 'a>,
//     ast: &ASTList<'a>,
// ) -> Result<(), E> {
//     ast.into_iter()
//         .filter_map(|ast| match ast {
//             AST::Declaration(b) => match Box::as_ref(b) {
//                 Declaration::Cell(f) => Some(extra::MAsFunction::Cell(f)),
//                 _ => None,
//             },
//             AST::Step(b) => Some(extra::MAsFunction::Step(Box::as_ref(b))),
//             _ => None,
//         })
//         // extract only the terms that matter
//         // that is the declarations of cells and steps
//         // and turn them into a MAsFunction to generically take care of them
//         .try_for_each(|fun| {
//             let SnN { span, name } = fun.name();
//             if env.function_hash.contains_key(&name) {
//                 err(merr(
//                     *span,
//                     f!("the step/cell/function name {} is already in use", &name),
//                 ))
//             } else {
//                 // the input sorts (will gracefully error out later if a sort is undefined)
//                 let _input_sorts: Result<Vec<_>, _> = fun
//                     .args()
//                     .into_iter()
//                     .map(|idn| get_sort(env, *idn.span, idn.name))
//                     .collect();
//                 // the output sort
//                 let _output_sort = {
//                     let idn = fun.out();
//                     get_sort(env, *idn.span, idn.name)
//                 }?;
//                 // built an uninitialized function
//                 // let fun = Function::new_uninit(
//                 //     env.container,
//                 //     // Some(name),
//                 //     // Some(input_sorts?),
//                 //     // Some(output_sort),
//                 // );
//                 let fun: Function<'bump> = env.container.allocate_uninit().into();

//                 // add the function to the list of things to initialize
//                 let err_check = env.functions_initialize.insert(fun.into(), None);
//                 // errors out if it is already in the list
//                 // NB: no UB because "uninitialized" is another state.
//                 // (might "gracefully" crash later though)
//                 if let Some(_) = err_check {
//                     err(merr(
//                         *span,
//                         f!("already in the list of things to initialize"),
//                     ))?;
//                 }

//                 // add the function the map of function for faster parsing
//                 env.function_hash
//                     .insert(fun.name().to_string(), fun)
//                     .ok_or_else(|| {
//                         merr(
//                             *span,
//                             f!("!UNREACHABLE!(line {} in {}; {})", line!(), file!(), name),
//                         )
//                     })
//                     .map(|_| ())
//             }
//         })
// }