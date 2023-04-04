pub mod formula_iterator;
pub mod formula_trait;
pub mod formula_expander;
// pub mod formula_user;



use super::{
    function::Function,
};

// #[derive(Clone)]
// pub struct Evaluator<'bump> {
//     msg: Function<'bump>,
//     cond: Function<'bump>,
//     ta: bool,
// }

// impl<'bump> Evaluator<'bump> {
//     pub fn msg<T, U>(&self, ctx: &T, arg: U) -> U
//     where
//         T: FormulaUser<U>,
//     {
//         if self.ta {
//             self.msg.cf(ctx, [arg])
//         } else {
//             arg
//         }
//     }
//     pub fn cond<T, U>(&self, ctx: &T, arg: U) -> U
//     where
//         T: FormulaUser<U>,
//     {
//         if self.ta {
//             self.cond.cf(ctx, [arg])
//         } else {
//             arg
//         }
//     }

//     pub fn new(env: &Environement) -> Option<Self> {
//         Some(Evaluator {
//             msg: env.get_f(EVAL_MSG_NAME)?.clone(),
//             cond: env.get_f(EVAL_COND_NAME)?.clone(),
//             ta: !env.no_ta(),
//         })
//     }
// }