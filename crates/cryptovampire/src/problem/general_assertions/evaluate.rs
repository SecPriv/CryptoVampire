use std::collections::BTreeMap;
use std::sync::Arc;

use itertools::Itertools;
use log::trace;

use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::{Axiom, Rewrite, RewriteKind};
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{self, meq};
use crate::formula::function::builtin::{EQUALITY, IF_THEN_ELSE};
use crate::formula::function::inner::term_algebra::TermAlgebra;
use crate::formula::function::inner::term_algebra::connective::{BaseConnective, Connective};
use crate::formula::function::inner::term_algebra::quantifier::{InnerQuantifier, Quantifier};
use crate::formula::function::traits::FixedSignature;
use crate::formula::function::{Function, InnerFunction};
use crate::formula::manipulation::FrozenOVSubstF;
use crate::formula::sort::builtins::{BOOL, CONDITION, MESSAGE};
use crate::formula::sort::{FOSort, Sort};
use crate::formula::utils::Applicable;
use crate::formula::variable::{Variable, from_usize, sorts_to_variables};
use crate::problem::problem::Problem;
use crate::{mexists, mforall};

pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    let bool = *BOOL;
    let msg = *MESSAGE;
    let cond = *CONDITION;

    assertions.push(Axiom::Comment("evaluate".into()));

    let relevant_functions = pbl
        .functions()
        .iter()
        .filter_map(|f| match f.as_inner() {
            InnerFunction::TermAlgebra(TermAlgebra::Function(b)) => {
                assert!(
                    b.as_fixed_signature().out.is_evaluatable(),
                    "not evaluatable"
                );
                Some((f, b))
            }
            _ => None,
        })
        .collect_vec();

    // [(Base Sort, Evaluated Sort)]
    let relevant_sorts = pbl
        .sorts()
        .iter()
        .filter_map(|sort| {
            sort.maybe_evaluated_sort()
                .map(|evaluated_sort| (sort, evaluated_sort))
        })
        .collect_vec();

    declarations.extend(
        relevant_sorts
            .iter()
            .filter(|(_, se)| se != &BOOL.as_sort())
            .map(|(sort, evalluated_sort)| {
                if env.is_symbolic_realm() {
                    Declaration::Sort(*evalluated_sort)
                } else {
                    Declaration::SortAlias {
                        from: **sort,
                        to: *evalluated_sort,
                    }
                }
            }),
    );
    if env.is_evaluated_realm() {
        // bool and condition are dealt with separatly
        declarations.push(Declaration::SortAlias {
            to: CONDITION.as_sort(),
            from: BOOL.as_sort(),
        })
    }

    // declare the evaluation functions
    declarations.extend(
        pbl.evaluator()
            .iter_functions()
            .map(Declaration::FreeFunction),
    );

    // declare the evaluation of quantifiers
    // symbolic_quantifiers(assertions, pbl, env, declarations);

    if env.is_evaluated_realm() {
        assertions.extend(
            pbl.evaluator()
                .iter()
                .map(|(s, fun)| {
                    mforall!(x!1:s; {
                        EQUALITY.f([fun.f([x]), x.into()])
                    })
                })
                .map(Axiom::base),
        );
        // return;
    } else {
        if !env.no_bitstring_functions() {
            declarations.extend(
                relevant_functions
                    .iter()
                    .map(|(_, b)| b.eval_fun())
                    .map(Declaration::FreeFunction),
            );

            // assertions.extend(relevant_functions.iter().map())
            declarations.reserve(relevant_sorts.len());
            let rewrite_funs: BTreeMap<FOSort<'bump>, _> = relevant_sorts
                .into_iter()
                .map(|(s, s2)| {
                    if s2 == bool {
                        (s, RewriteKind::Bool)
                    } else {
                        let fun = Function::new_rewrite_function(pbl.container(), s2);
                        declarations.push(Declaration::FreeFunction(fun));
                        (s, RewriteKind::Other(fun))
                    }
                })
                .map(|(s, e)| ((*s).into(), e))
                .collect();

            assertions.extend(
                relevant_functions
                    .iter()
                    .map(|(f, ibf)| {
                        let ev = ibf.eval_fun();
                        let rw_kind = rewrite_funs.get(&ibf.out().into()).unwrap();
                        let vars: Arc<[_]> = sorts_to_variables(0, ibf.args());
                        trace!("evaluating -> {}", f.name());
                        let out = Rewrite {
                            kind: *rw_kind,
                            vars: vars.clone(),
                            pre: pbl
                                .evaluator()
                                .eval(f.apply(vars.iter().map(|v| v.into_formula()))),
                            post: ev
                                .f(vars.iter().map(|v| pbl.evaluator().eval(v.into_aformula()))),
                        };
                        trace!("{:?}", out);
                        out
                    })
                    .map(|r| Axiom::Rewrite {
                        rewrite: Box::new(r),
                    }),
            )
        }

        if env.use_legacy_evaluate() {
            assertions.extend(
                relevant_functions
                    .iter()
                    .map(|(&f, ibf)| {
                        let vars1: Vec<_> = sorts_to_variables(0, ibf.args());
                        let vars2 = vars1
                            .iter()
                            .map(|&v| v + from_usize(vars1.len()))
                            .collect_vec();

                        let premise =
                            formula::ands(vars1.iter().zip(vars2.iter()).map(|(v1, _v2)| {
                                meq(pbl.evaluator().eval(v1), pbl.evaluator().eval(v1))
                            }));
                        let conclusion = meq(
                            pbl.evaluator().eval(f.f(&vars1)), //.map(|v| v.into_formula()))),
                            pbl.evaluator().eval(f.f(&vars2)),
                        );
                        mforall!(vars1.into_iter().chain(vars2.into_iter()), {
                            premise >> conclusion
                        })
                    })
                    .map(Axiom::base),
            )
        }
    }

    for function in pbl.functions() {
        match function.as_inner() {
            InnerFunction::TermAlgebra(ta) => {
                match ta {
                    TermAlgebra::Function(_) => continue, // already done
                    TermAlgebra::Cell(_) | TermAlgebra::Macro(_) | TermAlgebra::NameCaster(_) => continue, // nothing specific to be done here
                    TermAlgebra::IfThenElse(_) => {
                        assertions.push(Axiom::base(mforall!(c!0:cond, l!1:msg, r!2:msg; {
                            meq(pbl.evaluator().eval(function.f([c, l, r])),
                                IF_THEN_ELSE.f([c, l, r].into_iter().map(|v| pbl.evaluator().eval(v))))
                        })))
                    },
                    TermAlgebra::Quantifier(q) => generate_quantifier(assertions, declarations, env, pbl, function, q),
                    TermAlgebra::Condition(connective) => generate_connectives( function, connective, assertions, pbl, msg, cond),
                }
            }
            _ => continue,
        }
    }
}

fn generate_connectives<'bump>(
    function: &Function<'bump>,
    connective: &Connective,
    assertions: &mut Vec<Axiom<'bump>>,
    pbl: &Problem<'bump>,
    msg: Sort<'bump>,
    cond: Sort<'bump>,
) {
    match connective {
        Connective::Equality(_) => assertions.push(Axiom::base(mforall!(a!0:msg, b!1:msg; {
            meq(
            pbl.evaluator().eval(function.apply([a, b])),
                meq(pbl.evaluator().eval(a), pbl.evaluator().eval(b)))
        }))),
        Connective::BaseConnective(BaseConnective::Not) => {
            assertions.push(Axiom::base(mforall!(a!0:cond; {
                pbl.evaluator().eval(function.apply([a])) >>
                    !pbl.evaluator().eval(a)
            })))
        }
        Connective::BaseConnective(c) => {
            let signature = c.as_fixed_signature();
            let f_eval = c.evaluated();
            let args = signature
                .args
                .iter()
                .zip(0..)
                .map(|(&sort, id)| Variable { id, sort })
                .collect_vec();
            assertions.push(Axiom::base(mforall!(args.clone(), {
                meq(
                    pbl.evaluator().eval(function.f(&args)),
                    f_eval.f(args.iter().map(|v| pbl.evaluator().eval(v))),
                )
            })))
        }
    }
}

pub fn generate_quantifier<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    _env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    function: &Function<'bump>,
    q: &Quantifier<'bump>,
) {
    match q.inner() {
        InnerQuantifier::Forall { content } => {
            assertions.push(Axiom::base(mforall!(q.free_variables.iter().cloned(), {
                pbl.evaluator()
                    .eval(function.apply(q.free_variables.iter().map(|v| v.into_formula())))
                    >> mforall!(q.bound_variables.iter().cloned(), {
                        pbl.evaluator().eval(content)
                    })
            })))
        }
        InnerQuantifier::Exists { content } => {
            assertions.push(Axiom::base(mforall!(q.free_variables.iter().cloned(), {
                pbl.evaluator()
                    .eval(function.apply(q.free_variables.iter().map(|v| v.into_formula())))
                    >> mexists!(q.bound_variables.iter().cloned(), {
                        pbl.evaluator().eval(content)
                    })
            })))
        }
        InnerQuantifier::FindSuchThat {
            condition,
            success,
            faillure,
        } => {
            let skolems = q
                .bound_variables
                .iter()
                .map(|Variable { sort, .. }| {
                    Function::new_skolem(
                        pbl.container(),
                        q.free_variables.iter().map(|v| v.sort),
                        *sort,
                    )
                })
                .collect_vec();

            declarations.extend(skolems.iter().map(|f| Declaration::FreeFunction(*f)));

            let substitution = {
                let subst_source = q.bound_variables.iter().map(|v| v.id);
                let subst_target = skolems.iter().map(|f| f.f(q.free_variables.iter()));

                FrozenOVSubstF::from_iter(subst_source.zip_eq(subst_target).map_into())
            };

            let applied_condition = condition.apply_substitution2(&substitution);
            let applied_l = success.apply_substitution2(&substitution);
            let applied_r = faillure.apply_substitution2(&substitution);

            assertions.extend(
                [
                    mforall!(q.free_variables.iter().cloned(), {
                        mforall!(q.bound_variables.iter().cloned(), {
                            !pbl.evaluator().eval(condition)
                        }) | pbl.evaluator().eval(applied_condition.clone())
                    }),
                    mforall!(q.free_variables.iter().cloned(), {
                        meq(
                            pbl.evaluator().eval(
                                function.apply(q.free_variables.iter().map(|v| v.into_formula())),
                            ),
                            IF_THEN_ELSE.apply(
                                [applied_condition, applied_l, applied_r]
                                    .into_iter()
                                    .map(|f| pbl.evaluator().eval(f)),
                            ),
                        )
                    }),
                ]
                .map(Axiom::base),
            )
        }
    }
}
