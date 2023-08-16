use std::{collections::HashMap, sync::Arc};

use itertools::Itertools;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{
            axioms::{Axiom, Rewrite, RewriteKind},
            declare::Declaration,
        },
        formula::{self, meq},
        function::{
            builtin::{EQUALITY, IF_THEN_ELSE},
            inner::term_algebra::{
                base_function::BaseFunction,
                connective::{BaseConnective, Connective},
                quantifier::{InnerQuantifier, Quantifier},
                TermAlgebra,
            },
            Function, InnerFunction,
        },
        sort::{
            builtins::{BOOL, CONDITION, MESSAGE},
            Sort,
        },
        variable::{sorts_to_variables, Variable},
    },
    mexists, mforall,
    problem::problem::Problem,
};

pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    let bool = BOOL.clone();
    let msg = MESSAGE.clone();
    let cond = CONDITION.clone();

    assertions.push(Axiom::Comment("evaluate".into()));

    let relevant_functions = pbl
        .functions
        .iter()
        .filter_map(|f| match f.as_inner() {
            InnerFunction::TermAlgebra(TermAlgebra::Function(BaseFunction::Base(b))) => {
                assert_eq!(f.fast_outsort().map(|s| s.is_evaluatable()), Some(true));
                Some((f, b))
            }
            _ => None,
        })
        .collect_vec();

    let relevant_sorts = pbl
        .sorts
        .iter()
        .filter_map(|sort| {
            sort.evaluated_sort()
                .map(|evaluated_sort| (sort, evaluated_sort))
        })
        .collect_vec();

    declarations.extend(relevant_sorts.iter().map(|(sort, evalluated_sort)| {
        if env.is_symbolic_realm() {
            Declaration::Sort(*evalluated_sort)
        } else {
            Declaration::SortAlias {
                from: **sort,
                to: *evalluated_sort,
            }
        }
    }));
    // declare the evaluation functions
    declarations.extend(
        pbl.evaluator
            .functions()
            .values()
            .cloned()
            .map(Declaration::FreeFunction),
    );

    if env.is_evaluated_realm() {
        assertions.extend(
            pbl.evaluator
                .functions()
                .iter()
                .map(|(s, fun)| {
                    mforall!(x!1:*s; {
                        EQUALITY.f_a([fun.f_a([x]), x.into()])
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
            let rewrite_funs: HashMap<_, _> = relevant_sorts
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
                .collect();

            assertions.extend(
                relevant_functions
                    .iter()
                    .map(|(f, ibf)| {
                        let ev = ibf.eval_fun();
                        let rw_kind = rewrite_funs.get(&ibf.out()).unwrap();
                        let vars: Arc<[_]> = sorts_to_variables(0, ibf.args());
                        Rewrite {
                            kind: rw_kind.clone(),
                            vars: vars.clone(),
                            pre: pbl
                                .evaluator
                                .eval(f.f(vars.iter().map(|v| v.into_formula()))),
                            post: ev
                                .f_a(vars.iter().map(|v| pbl.evaluator.eval(v.into_aformula()))),
                        }
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
                        let vars2 = vars1.iter().map(|&v| v + vars1.len()).collect_vec();

                        let premise =
                            formula::ands(vars1.iter().zip(vars2.iter()).map(|(v1, _v2)| {
                                meq(pbl.evaluator.eval(v1), pbl.evaluator.eval(v1))
                            }));
                        let conclusion = meq(
                            pbl.evaluator.eval(f.f_a(&vars1)), //.map(|v| v.into_formula()))),
                            pbl.evaluator.eval(f.f_a(&vars2)),
                        );
                        mforall!(vars1.into_iter().chain(vars2.into_iter()), {
                            premise >> conclusion
                        })
                    })
                    .map(Axiom::base),
            )
        }

        for function in &pbl.functions {
            match function.as_inner() {
                InnerFunction::TermAlgebra(ta) => {
                    match ta {
                    TermAlgebra::Function(_) => continue, // already done
                    TermAlgebra::Cell(_) | TermAlgebra::Input(_) | TermAlgebra::Name(_) | TermAlgebra::NameCaster(_) => continue, // nothing specific to be done here
                    TermAlgebra::IfThenElse(_) => {
                        assertions.push(Axiom::base(mforall!(c!0:cond, l!1:msg, r!2:msg; {
                            pbl.evaluator.eval(function.f_a([c, l, r]))
                                >> IF_THEN_ELSE.f_a([c, l, r].into_iter().map(|v| pbl.evaluator.eval(v)))
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
        Connective::Equality(_) => assertions.push(Axiom::base(mforall!(a!0:msg, b!0:msg; {
            pbl.evaluator.eval(function.f([a.clone(), b.clone()])) >>
                meq(pbl.evaluator.eval(a), pbl.evaluator.eval(b))
        }))),
        Connective::BaseConnective(BaseConnective::Not) => {
            assertions.push(Axiom::base(mforall!(a!0:cond; {
                pbl.evaluator.eval(function.f([a.clone()])) >>
                    !pbl.evaluator.eval(a)
            })))
        }
        Connective::BaseConnective(c) => {
            assertions.push(Axiom::base(mforall!(a!0:cond, b!0:cond; {
                pbl.evaluator.eval(function.f_a([a, b])) >>
                    c.evaluated().f_a([pbl.evaluator.eval(a), pbl.evaluator.eval(b)])
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
                pbl.evaluator
                    .eval(function.f(q.free_variables.iter().map(|v| v.into_formula())))
                    >> mforall!(q.bound_variables.iter().cloned(), {
                        pbl.evaluator.eval(content)
                    })
            })))
        }
        InnerQuantifier::Exists { content } => {
            assertions.push(Axiom::base(mforall!(q.free_variables.iter().cloned(), {
                pbl.evaluator
                    .eval(function.f(q.free_variables.iter().map(|v| v.into_formula())))
                    >> mexists!(q.bound_variables.iter().cloned(), {
                        pbl.evaluator.eval(content)
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

            let subst_source = q.bound_variables.iter().map(|v| v.id).collect_vec();
            let subst_target = skolems
                .iter()
                .map(|f| f.f_a(q.free_variables.iter()))
                .collect_vec();

            let applied_condition = condition
                .into_inner()
                .apply_substitution(subst_source.clone(), &subst_target);
            let applied_l = success
                .into_inner()
                .apply_substitution(subst_source.clone(), &subst_target);
            let applied_r = faillure
                .into_inner()
                .apply_substitution(subst_source.clone(), &subst_target);

            assertions.extend(
                [
                    mforall!(
                        q.free_variables
                            .iter()
                            .chain(q.bound_variables.iter())
                            .cloned(),
                        {
                            pbl.evaluator.eval(condition)
                                >> pbl.evaluator.eval(applied_condition.clone())
                        }
                    ),
                    mforall!(q.free_variables.iter().cloned(), {
                        meq(
                            pbl.evaluator.eval(
                                function.f(q.free_variables.iter().map(|v| v.into_formula())),
                            ),
                            IF_THEN_ELSE.f([applied_condition, applied_l, applied_r]
                                .into_iter()
                                .map(|f| pbl.evaluator.eval(f))),
                        )
                    }),
                ]
                .map(Axiom::base),
            )
        }
    }
}
