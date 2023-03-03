use super::{
    builtins::functions::{EVAL_COND_NAME, EVAL_MSG_NAME},
    env::Environement,
    formula_user::FormulaUser,
    function::Function,
};

#[derive(Clone)]
pub struct Evaluator {
    msg: Function,
    cond: Function,
    ta: bool,
}

impl Evaluator {
    pub fn msg<T, U>(&self, ctx: &T, arg: U) -> U
    where
        T: FormulaUser<U>,
    {
        if self.ta {
            self.msg.cf(ctx, [arg])
        } else {
            arg
        }
    }
    pub fn cond<T, U>(&self, ctx: &T, arg: U) -> U
    where
        T: FormulaUser<U>,
    {
        if self.ta {
            self.cond.cf(ctx, [arg])
        } else {
            arg
        }
    }

    pub fn new(env: &Environement) -> Option<Self> {
        Some(Evaluator {
            msg: env.get_f(EVAL_MSG_NAME)?.clone(),
            cond: env.get_f(EVAL_COND_NAME)?.clone(),
            ta: !env.no_ta(),
        })
    }
}
