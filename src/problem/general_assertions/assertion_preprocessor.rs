use std::borrow::Cow;

use itertools::Itertools;

use crate::formula::{
    formula::{ARichFormula, RichFormula},
    function::{inner::evaluate::Evaluator, traits::MaybeEvaluatable},
    variable::Variable,
};

pub fn preprocess<'bump>(
    assertion: ARichFormula<'bump>,
    env: &Evaluator<'bump>,
) -> ARichFormula<'bump> {
    preprocess_before_eval(assertion.as_ref(), env)
        .as_ref()
        .into()
}

fn preprocess_before_eval<'a, 'bump>(
    assertion: &'a RichFormula<'bump>,
    env: &Evaluator<'bump>,
) -> Cow<'a, RichFormula<'bump>> {
    match assertion {
        RichFormula::Var(_) => Cow::Borrowed(assertion),
        RichFormula::Fun(fun, args) if fun.as_ref().is_evaluate() => {
            Cow::Owned(preprocess_after_eval(&args[0], env))
        }
        RichFormula::Fun(fun, args) => {
            let n_args = args
                .iter()
                .map(|arg| preprocess_before_eval(arg, env))
                .collect_vec();
            if n_args.iter().all(|cow| match cow {
                Cow::Borrowed(_) => true,
                _ => false,
            }) {
                Cow::Borrowed(assertion)
            } else {
                Cow::Owned(RichFormula::Fun(
                    *fun,
                    args.iter().map(|cow| cow.as_ref().into()).collect(),
                ))
            }
        }
        RichFormula::Quantifier(q, arg) => {
            let arg = preprocess_before_eval(arg.as_ref(), env);
            match arg {
                Cow::Borrowed(_) => Cow::Borrowed(assertion),
                Cow::Owned(arg) => Cow::Owned(RichFormula::Quantifier(q.clone(), arg.into())),
            }
        }
    }
}

fn preprocess_after_eval<'bump>(
    assertion: &RichFormula<'bump>,
    env: &Evaluator<'bump>,
) -> RichFormula<'bump> {
    match assertion {
        RichFormula::Var(v) if v.sort().is_evaluatable() => RichFormula::Var(Variable {
            sort: v.sort().evaluated_sort().unwrap(),
            ..*v
        }),
        RichFormula::Fun(fun, args) => match fun.as_ref().maybe_get_evaluated() {
            Some(f) => RichFormula::Fun(
                f,
                args.iter()
                    .map(|arg| preprocess_after_eval(arg, env).into_arc())
                    .collect(),
            ),
            None => env.eval(assertion).into_inner(),
        },
        RichFormula::Quantifier(_, _) => unreachable!(),
        _ => env.eval(assertion).into_inner(),
    }
}
