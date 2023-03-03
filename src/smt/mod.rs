use crate::formula::{env::Environement, builtins::functions::{EVAL_COND_NAME, EVAL_MSG_NAME}};

use self::smt::SmtFormula;

pub mod macros;
pub mod smt;
pub mod writer;

// pub fn get_eval_msg(env:&Environement) -> impl Clone + Fn(SmtFormula) -> SmtFormula {
//     let eval = env.get_f(EVAL_MSG_NAME).unwrap().clone();
//     let no_ta = env.no_ta();
//     move |f| {
//         if !no_ta {
//             SmtFormula::Fun(eval.clone(), vec![f])
//         } else {
//             f
//         }
//     }
// }

// pub fn get_eval_cond(env:&Environement) -> impl Clone + Fn(SmtFormula) -> SmtFormula {
//     let eval = env.get_f(EVAL_COND_NAME).unwrap().clone();
//     // let ctrue = env.get_f(CTRUE_NAME).unwrap().clone();
//     let no_ta = env.no_ta();
//     move |f| {
//         if !no_ta {
//             SmtFormula::Fun(eval.clone(), vec![f])
//         } else {
//             SmtFormula::Fun(eval.clone(), vec![f])
//         }
//     }
// }