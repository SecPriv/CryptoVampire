use std::collections::HashMap;

use itertools::Itertools;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{
            axioms::{Axiom, Rewrite, RewriteKind},
            declare::Declaration,
        },
        formula::{meq, RichFormula},
        function::{
            builtin::IF_THEN_ELSE,
            term_algebra::{
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
    if env.no_evaluate() {
        return;
    }

    let bool = BOOL.clone();
    let msg = MESSAGE.clone();
    let cond = CONDITION.clone();

    assertions.push(Axiom::Comment("evaluate".into()));

    let relevant_functions = pbl
        .functions
        .iter()
        .filter_map(|f| match f.as_ref() {
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
        .filter_map(|s| s.evaluated_sort().map(|s2| (s, s2)))
        .collect_vec();

    declarations.extend(relevant_sorts.iter().map(|(s, s2)| {
        if env.use_bitstring() {
            Declaration::Sort(*s2)
        } else {
            Declaration::SortAlias { from: **s, to: *s2 }
        }
    }));

    if env.use_bitstring() {
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
                    let vars = sorts_to_variables(0, ibf.args());
                    Rewrite {
                        kind: rw_kind.clone(),
                        vars: vars.clone(),
                        pre: pbl
                            .evaluator
                            .eval(f.f(vars.iter().map(|v| v.into_formula()))),
                        post: ev.f(vars.iter().map(|v| pbl.evaluator.eval(v.into_formula()))),
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
                    let vars1 = sorts_to_variables(0, ibf.args());
                    let vars2 = vars1.iter().map(|&v| v + vars1.len()).collect_vec();

                    let premise =
                        RichFormula::ands(vars1.iter().zip(vars2.iter()).map(|(v1, _v2)| {
                            meq(
                                pbl.evaluator.eval(v1.into_formula()),
                                pbl.evaluator.eval(v1.into_formula()),
                            )
                        }));
                    let conclusion = meq(
                        pbl.evaluator
                            .eval(f.f(vars1.iter().map(|v| v.into_formula()))),
                        pbl.evaluator
                            .eval(f.f(vars2.iter().map(|v| v.into_formula()))),
                    );
                    mforall!(vars1.into_iter().chain(vars2.into_iter()), {
                        premise >> conclusion
                    })
                })
                .map(Axiom::base),
        )
    }

    for function in &pbl.functions {
        match function.as_ref() {
            InnerFunction::TermAlgebra(ta) => {
                match ta {
                    TermAlgebra::Function(_) => continue, // already done
                    TermAlgebra::Cell(_) | TermAlgebra::Input(_) | TermAlgebra::Name(_) => continue, // nothing specific to be done here
                    TermAlgebra::IfThenElse(_) => {
                        assertions.push(Axiom::base(mforall!(c!0:cond, l!1:msg, r!2:msg; {
                            pbl.evaluator.eval(function.f([c.clone(), l.clone(), r.clone()]))
                                >> IF_THEN_ELSE.f([c, l, r].into_iter().map(|v| pbl.evaluator.eval(v)))
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
                pbl.evaluator.eval(function.f([a.clone(), b.clone()])) >>
                    c.evaluated().f([pbl.evaluator.eval(a), pbl.evaluator.eval(b)])
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
                        pbl.evaluator.eval(*content.clone())
                    })
            })))
        }
        InnerQuantifier::Exists { content } => {
            assertions.push(Axiom::base(mforall!(q.free_variables.iter().cloned(), {
                pbl.evaluator
                    .eval(function.f(q.free_variables.iter().map(|v| v.into_formula())))
                    >> mexists!(q.bound_variables.iter().cloned(), {
                        pbl.evaluator.eval(*content.clone())
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
                .map(|f| f.f(q.free_variables.iter().map(|v| v.into_formula())))
                .collect_vec();

            let applied_condition = condition
                .clone()
                .apply_substitution(subst_source.clone(), &subst_target);
            let applied_l = success
                .clone()
                .apply_substitution(subst_source.clone(), &subst_target);
            let applied_r = faillure
                .clone()
                .apply_substitution(subst_source.clone(), &subst_target);

            assertions.extend(
                [
                    mforall!(
                        q.free_variables
                            .iter()
                            .chain(q.bound_variables.iter())
                            .cloned(),
                        {
                            pbl.evaluator.eval(*condition.clone())
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
