use std::borrow::Cow;

use itertools::Itertools;

use crate::formula::formula::{ARichFormula, RichFormula};
use crate::formula::function::inner::evaluate::Evaluator;
use crate::formula::function::inner::term_algebra::quantifier::{InnerQuantifier, Quantifier};
use crate::formula::function::traits::MaybeEvaluatable;
use crate::formula::manipulation::FrozenSubstF;
use crate::formula::variable::Variable;
use crate::formula::{self};

pub fn propagate_evaluate<'bump>(
    assertion: &RichFormula<'bump>,
    env: &Evaluator<'bump>,
) -> ARichFormula<'bump> {
    preprocess_before_eval(assertion, env).as_ref().into()
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
            if n_args.iter().all(|cow| matches!(cow, Cow::Borrowed(_))) {
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
        RichFormula::Var(v) if v.sort().is_evaluatable() => Some(RichFormula::Var(Variable {
            sort: v.sort().maybe_evaluated_sort().unwrap(),
            ..*v
        })),
        RichFormula::Fun(fun, args) => match fun.as_ref().maybe_get_evaluated() {
            Some(f) => Some(RichFormula::Fun(
                f,
                args.iter()
                    .map(|arg| preprocess_after_eval(arg, env).into_arc())
                    .collect(),
            )),
            None => match fun
                .precise_as_term_algebra()
                .and_then(|ta| ta.as_quantifier())
            {
                Some(Quantifier {
                    bound_variables,
                    free_variables,
                    id: _,
                    inner,
                }) => match inner {
                    InnerQuantifier::FindSuchThat { .. } => None,
                    InnerQuantifier::Forall { content } | InnerQuantifier::Exists { content } => {
                        Some({
                            let content = content.apply_substitution2(&FrozenSubstF::new_from(
                                bound_variables.iter().map(Variable::id).collect_vec(),
                                args,
                            ));
                            let content = preprocess_after_eval(content.as_ref(), env);

                            let q = match inner {
                                InnerQuantifier::Forall { .. } => {
                                    formula::quantifier::Quantifier::Forall {
                                        variables: free_variables.clone(),
                                    }
                                }
                                InnerQuantifier::Exists { .. } => {
                                    formula::quantifier::Quantifier::Exists {
                                        variables: free_variables.clone(),
                                    }
                                }
                                _ => unreachable!(),
                            };

                            RichFormula::Quantifier(q, content.into())
                        })
                    }
                },
                None => None,
            },
        },
        RichFormula::Quantifier(_, _) => unreachable!(),
        _ => None,
    }
    .unwrap_or_else(|| env.eval(assertion).into_inner())
}
