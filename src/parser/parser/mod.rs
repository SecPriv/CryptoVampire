pub mod guard;
pub mod parsable_trait;
pub mod state;

mod declare;
pub use declare::{declare_fun_step_cell_let, declare_sorts};

mod parsing_environement;
pub use parsing_environement::{Environement, Macro, get_function, get_sort, FunctionCache};
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
