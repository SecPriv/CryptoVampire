use std::collections::{BTreeMap, HashSet};
use std::sync::Arc;

use itertools::{Itertools, izip};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::UsedVariableIterator;
use utils::econtinue_if;

use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::{Axiom, Rewrite, RewriteKind};
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{self, ARichFormula, RichFormula, meq};
use crate::formula::function::builtin::{
    BUILT_IN_FUNCTIONS, EQUALITY, FALSE_F, IF_THEN_ELSE, TRUE_F,
};
use crate::formula::function::inner::term_algebra::TermAlgebra;
use crate::formula::function::inner::term_algebra::connective::{BaseConnective, Connective};
use crate::formula::function::inner::term_algebra::quantifier::{InnerQuantifier, Quantifier};
use crate::formula::function::traits::FixedSignature;
use crate::formula::function::{Function, InnerFunction};
use crate::formula::manipulation::{FrozenOVSubstF, FrozenSubstF};
use crate::formula::sort::builtins::{BOOL, CONDITION, MESSAGE};
use crate::formula::sort::{FOSort, Sort};
use crate::formula::utils::Applicable;
use crate::formula::variable::{IntoVariableIter, Variable, from_usize, sorts_to_variables, uvar};
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
        // The symbolic realm does this for *all* [TermAlgebra::Function]s in
        // the `else` branch below. In the evaluated realm we must do it for the
        // TA functions whose evaluated twin is a built-in that is already
        // declared (e.g. `s_happens`/`s_lt` -> `happens`/`lt`), otherwise
        // `evaluate_cond (s_happens t)` / `evaluate_msg (s_foo m)` are left
        // with no definition linking them to the evaluated function. We
        // restrict to built-in twins because user TA functions get a fresh
        // `eval$...` that is only declared in the symbolic realm (referencing
        // it here would be a dangling symbol in the evaluated realm).
        assertions.extend(
            relevant_functions
                .iter()
                .filter(|(_, ibf)| BUILT_IN_FUNCTIONS.contains(&ibf.eval_fun()))
                .map(|(f, ibf)| {
                    let ev = ibf.eval_fun();
                    let vars: Arc<[_]> = sorts_to_variables(0, ibf.args());
                    Axiom::base(mforall!(vars.iter().cloned(), {
                        meq(
                            pbl.evaluator()
                                .eval(f.apply(vars.iter().map(|v| v.into_formula()))),
                            ev.f(vars.iter().map(|v| pbl.evaluator().eval(v.into_aformula()))),
                        )
                    }))
                }),
        );
        // return;
    } else {
        if !env.no_bitstring_functions() {
            // don't redeclare eval twins that are already first-class builtins
            // in the problem (e.g. `happens`/`lt` are used as `eval_fun` of
            // `s_happens`/`s_lt` but are also declared by the main declare
            // loop); declaring them twice makes the solvers reject the file.
            declarations.extend(
                relevant_functions
                    .iter()
                    .map(|(_, b)| b.eval_fun())
                    .filter(|f| !pbl.functions().contains(f))
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

    // Experimental "pairwise find-such-that FA" axiom (see [pairwise_find_fa]).
    if env.pairwise_find_fa() {
        pairwise_find_fa(assertions, declarations, env, pbl);
    }
}

/// Emit the experimental pairwise find-such-that "FA" axioms (trusted).
///
/// For every two finds `f1`, `f2` of the problem whose variable signatures
/// match up to alpha-renaming (same arity and sorts, in the same order, for
/// both the free *and* the bound variables), assert a **skolem-free** pairing
/// axiom in the spirit of Squirrel's `fa` (see `src/core/traceTactics.ml`,
/// the `Term.Find` vs `Term.Find` case): the finds' bound variables are
/// `∀`-quantified, aligned positionally onto one fresh tuple `B` (e.g. `l`
/// becomes `k`), and the **unused** indices — those not occurring in `f1`'s
/// condition nor its then-branch (detected syntactically, *after* macro
/// expansion, so a dummy like the `j` in `mk!(i,j)=key(i)` is invisible) —
/// are handled by `∃`-absorption in the forward direction:
///
/// ```text
///   ∀F B.
///      ( c1(F,B) ⟹ ∃B_unused. c2(F,B) )        -- forward (unused indices may differ)
///    ∧ ( c2(F,B) ⟹ c1(F,B) )                   -- backward
///    ∧ ( c1(F,B) ∧ c2(F,B) ⟹ then1(F,B) = then2(F,B) )
///    ∧ ( else1 = else2 )                       -- Squirrel's 4th subgoal (blind)
///      → eval(f1(F)) = eval(f2(F))
/// ```
///
/// `F` is a fresh tuple of variables aligned positionally between the two
/// finds. NB: this is a **strengthening** of the raw `find` encoding,
/// gated behind `--pairwise-find-fa`.
///
/// **Fresh-variable assumption (soundness):** the fresh `F`/`B`/`b_unused`
/// tuples are allocated starting above [`Problem::max_var`], which only counts
/// ids visible in top-level term usage; ids hidden inside quantifier-function
/// bodies (e.g. the `bound_variables` of `ta$forall$N`) are *not* counted. For
/// every protocol tested so far those hidden ids stay below `max_var`, so the
/// fresh ids cannot collide with them, but this is an implicit assumption — new
/// encodings must keep all surviving ids `≤ pbl.max_var()` (or allocate fresh
/// ids that are provably disjoint).
fn pairwise_find_fa<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    _declarations: &mut Vec<Declaration<'bump>>,
    _env: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    let finds: Vec<(&Function<'bump>, &Quantifier<'bump>)> = pbl
        .functions()
        .iter()
        .filter_map(|f| match f.as_inner() {
            InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q))
                if q.inner().is_find_such_that() =>
            {
                Some((f, q))
            }
            _ => None,
        })
        .collect();

    // "same arity and sorts, in the same order" — both free *and* bound
    // variables must align so that one shared tuple of binders makes sense.
    let compatible = |a: &[Variable<'bump>], b: &[Variable<'bump>]| {
        let [asorts, bsorts] = [a, b].map(|x| x.iter().map(Variable::sort));
        a.len() == b.len() && izip!(asorts, bsorts).all(|(x, y)| x == y)
    };

    for ((f1, q1), (f2, q2)) in finds.iter().tuple_combinations() {
        econtinue_if!(
            !compatible(&q1.free_variables, &q2.free_variables)
                || !compatible(&q1.bound_variables, &q2.bound_variables)
        );

        let InnerQuantifier::FindSuchThat {
            condition: condition1,
            success: l1,
            faillure: r1,
        } = q1.inner()
        else {
            unreachable!()
        };

        let InnerQuantifier::FindSuchThat {
            condition: condition2,
            success: l2,
            faillure: r2,
        } = q2.inner()
        else {
            unreachable!()
        };

        // fresh aligned free tuple `F` and a shared aligned bound tuple `B`
        // (both finds' bound variables are aliased positionally onto it).
        let mut next = pbl.max_var();
        let mut fresh = |sort| {
            next += 1;
            Variable::new(next, sort)
        };
        let fv: Vec<Variable<'bump>> = q1.free_variables.iter().map(|v| fresh(v.sort)).collect();
        let bv: Vec<Variable<'bump>> = q1.bound_variables.iter().map(|v| fresh(v.sort)).collect();

        // "used" / "unused" split of each find's bound variables, by
        // syntactic occurrence in its condition and then-branch (Squirrel's
        // `occ_vars = get_vars c @ get_vars t`). Dummies that macro expansion
        // already rewrote away (e.g. `mk!(i,j)=key(i)`) count as unused and
        // are ∃-absorbed in the direction where they are the antecedent.
        let unused_of =
            |q: &Quantifier<'bump>, cond: &ARichFormula<'bump>, then_: &ARichFormula<'bump>| {
                // I believe this is more precise as variable capture by a
                // deeper quantifier but unused would still be considered as
                // unused (as far as I understand)
                let free_vars = [cond, then_]
                    .map(|x| x.as_expander().free_vars_iter())
                    .vars_id_iter()
                    .collect::<HashSet<_>>();
                // let used: HashSet<uvar> = UsedVariableIterator::with([cond, then_])
                // .map(|v| v.id)
                // .collect();
                bv.iter()
                    .enumerate()
                    .filter(|(i, _)| !free_vars.contains(&q.bound_variables[*i].id))
                    .map(|(_, v)| *v)
                    .collect::<Vec<_>>()
            };
        let b_unused1 = unused_of(q1, condition1, l1);
        let b_unused2 = unused_of(q2, condition2, l2);

        // substitute free → `F` and bound → `B`, for each find.
        let subst_for = |q: &Quantifier<'bump>| {
            FrozenOVSubstF::from_iter(
                q.free_variables
                    .iter()
                    .map(|v| v.id)
                    .zip(fv.iter().map(|v| v.into_formula().into()))
                    .chain(
                        q.bound_variables
                            .iter()
                            .map(|v| v.id)
                            .zip(bv.iter().map(|v| v.into_formula().into())),
                    )
                    .map_into(),
            )
        };
        let sub1 = subst_for(q1);
        let sub2 = subst_for(q2);

        let c1 = eval_condition(pbl, condition1.apply_substitution2(&sub1));
        let c2 = eval_condition(pbl, condition2.apply_substitution2(&sub2));
        let a1 = pbl.evaluator().eval(l1.apply_substitution2(&sub1));
        let a2 = pbl.evaluator().eval(l2.apply_substitution2(&sub2));
        let b1 = pbl.evaluator().eval(r1.apply_substitution2(&sub1));
        let b2 = pbl.evaluator().eval(r2.apply_substitution2(&sub2));

        let all_vars: Vec<Variable<'bump>> = fv.iter().chain(bv.iter()).copied().collect();

        // forward: c1 ⟹ ∃B_unused1. c2    (find1's unused indices may differ)
        let fwd_clause = c1.clone()
            >> (if b_unused1.is_empty() {
                c2.clone()
            } else {
                mexists!(b_unused1, { c2.clone() })
            });
        // backward: c2 ⟹ ∃B_unused2. c1    (find2's unused indices may differ)
        let bwd_clause = c2.clone()
            >> (if b_unused2.is_empty() {
                c1.clone()
            } else {
                mexists!(b_unused2, { c1.clone() })
            });
        // then: c1 ∧ c2 ⟹ then1 = then2
        let then_clause = (c1.clone() & c2.clone()) >> meq(a1.clone(), a2.clone());
        // else: Squirrel's 4th subgoal — blind `else1 = else2`
        let else_clause = (mforall!(bv, { !c1.clone() & !c2.clone() })) >> meq(b1, b2);

        let hypotheses = formula::ands([fwd_clause, bwd_clause, then_clause, else_clause]);

        let conclusion = meq(
            pbl.evaluator()
                .eval(f1.apply(fv.iter().map(|v| v.into_formula()))),
            pbl.evaluator()
                .eval(f2.apply(fv.iter().map(|v| v.into_formula()))),
        );

        // `all_vars` is moved into the outer binder.
        assertions.push(Axiom::base(mforall!(all_vars, {
            hypotheses >> conclusion
        })));
    }
}

/// Evaluate a find's condition and fully push `evaluate_cond` down through it
/// ([`push_down_condition`]), yielding a plain Boolean formula with no `ta$*`
/// combinators.
///
/// The emitted lemmas (user `lemma` statements) already go through
/// `propagate_evaluate` in `Problem::generate`, so keeping the pairwise-fa
/// clauses shaped the same way makes the lemma consequents *syntactically
/// isomorphic* to the fa-axiom hypothesis clauses — the bridge the solver's
/// E-matching can then see directly (instead of having to unfold the opaque
/// `ta$and`/`ta$or`/`ta$=` trees hidden under a single `evaluate_cond`).
fn eval_condition<'bump>(
    pbl: &Problem<'bump>,
    formula: impl Into<ARichFormula<'bump>>,
) -> ARichFormula<'bump> {
    let evaluated = pbl.evaluator().eval(formula);
    push_down_condition(&evaluated, pbl)
}

/// Push `evaluate_cond` down through a find-condition tree, turning the opaque
/// `ta$*` combinator soup (`ta$and`, `ta$or`, `ta$not`, `ta$implies`, `ta$=`,
/// `ta$true`/`ta$false`) into plain Boolean formulas, and expanding
/// `exec_pred!`-style parameterized `∀ Step`-conditions (term-algebra `Forall`
/// functions such as `ta$forall$2`/`3`/`4`) into literal `forall`s. The atomic
/// `s_lt` / `s_happens` leaves are kept wrapped (`evaluate_cond (s_lt …)` /
/// `evaluate_cond (s_happens …)`), and anything not structurally handled is
/// left untouched — the exact shape the emitted lemmas have.
///
/// NB: `crate::problem::general_assertions::assertion_preprocessor::propagate_evaluate`
/// already does most of this, but its quantifier branch assumes the term-
/// algebra quantifier's *bound* variables line up with the function's
/// application arguments, which is not the case for the `exec_pred!`-style
/// `ta$forall$N` (their `∀`-indices live in `bound_variables`, the `Step`
/// parameter in `free_variables`), so it panics — hence this self-contained
/// version used only for the pairwise-fa clauses.
///
/// **Strength note:** the emitted `ta$forall$2/3/4` folds (and `ta$not`) are
/// one-way implications (`evaluate_cond(ta$forall$N X) ⇒ ∀…`), unlike the
/// other connectives whose folds are equalities. Replacing
/// `evaluate_cond(ta$forall$N X)` with the literal `forall` therefore
/// *weakens* `c1`/`c2` in arbitrary SMT models. In the honest model the
/// equivalence `evaluate_cond(ta$forall$N X) ↔ ∀…` holds (the fold RHS is the
/// intended reading) and matches how the query/lemmas already render the same
/// `exec_pred!` block, so it restores — not corrupts — the honest meaning; the
/// widening happens only in non-honest models, consistent with this being a
/// documented trusted strengthening.
fn push_down_condition<'bump>(
    f: &ARichFormula<'bump>,
    pbl: &Problem<'bump>,
) -> ARichFormula<'bump> {
    // `f` must be `(evaluate_cond <Condition term>)`, as produced by
    // `pbl.evaluator().eval` on a Condition. Anything else is left as-is.
    let term = match f.as_inner() {
        RichFormula::Fun(fun, args) if matches!(fun.as_inner(), InnerFunction::Evaluate(e) if e.name() == "evaluate_cond") => {
            args[0].shallow_copy()
        }
        _ => return f.shallow_copy(),
    };
    match term.as_inner() {
        RichFormula::Var(_) | RichFormula::Quantifier(_, _) => f.shallow_copy(),
        RichFormula::Fun(tfun, targs) => match tfun.as_inner() {
            InnerFunction::TermAlgebra(TermAlgebra::Condition(c)) => match c {
                Connective::BaseConnective(BaseConnective::And) => formula::ands(
                    targs
                        .iter()
                        .map(|a| push_down_condition(&pbl.evaluator().eval(a.clone()), pbl)),
                ),
                Connective::BaseConnective(BaseConnective::Or) => formula::ors(
                    targs
                        .iter()
                        .map(|a| push_down_condition(&pbl.evaluator().eval(a.clone()), pbl)),
                ),
                Connective::BaseConnective(BaseConnective::Not) => {
                    !push_down_condition(&pbl.evaluator().eval(targs[0].clone()), pbl)
                }
                Connective::BaseConnective(BaseConnective::Implies) => {
                    let a = push_down_condition(&pbl.evaluator().eval(targs[0].clone()), pbl);
                    let b = push_down_condition(&pbl.evaluator().eval(targs[1].clone()), pbl);
                    a >> b
                }
                Connective::BaseConnective(BaseConnective::True) => {
                    RichFormula::Fun(*TRUE_F, Vec::<ARichFormula<'bump>>::new().into()).into()
                }
                Connective::BaseConnective(BaseConnective::False) => {
                    RichFormula::Fun(*FALSE_F, Vec::<ARichFormula<'bump>>::new().into()).into()
                }
                Connective::BaseConnective(BaseConnective::Iff) => f.shallow_copy(),
                Connective::Equality(_) => meq(
                    pbl.evaluator().eval(targs[0].clone()),
                    pbl.evaluator().eval(targs[1].clone()),
                ),
            },
            InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q)) => match &q.inner {
                InnerQuantifier::Forall { content } | InnerQuantifier::Exists { content } => {
                    // Expand a parameterized `∀ Step`-condition: the function's
                    // application arguments bind the quantifier's *free*
                    // variables, while the quantifier's own variables stay bound.
                    if q.free_variables.len() != targs.len() {
                        return f.shallow_copy(); // arity mismatch — keep it opaque
                    }
                    let subst = FrozenSubstF::new_from(
                        q.free_variables.iter().map(|v| v.id).collect_vec(),
                        targs,
                    );
                    let pushed = push_down_condition(
                        &pbl.evaluator().eval(content.apply_substitution2(&subst)),
                        pbl,
                    );
                    if matches!(&q.inner, InnerQuantifier::Forall { .. }) {
                        mforall!(q.bound_variables.iter().cloned(), { pushed })
                    } else {
                        mexists!(q.bound_variables.iter().cloned(), { pushed })
                    }
                }
                _ => f.shallow_copy(),
            },
            // `s_lt` / `s_happens` / any other leaf: keep `evaluate_cond`-wrapped.
            _ => f.shallow_copy(),
        },
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
            // Skolem functions must be named *deterministically*: they are
            // recreated on every problem (re)generation, but instances
            // discovered from a solver's previous output keep referring to the
            // old names. Deriving the name from the stable quantifier name
            // (rather than using a fresh unique name) keeps those references
            // resolving to a declared function.
            let skolems = q
                .bound_variables
                .iter()
                .enumerate()
                .map(|(i, Variable { sort, .. })| {
                    Function::new_skolem_named(
                        pbl.container(),
                        &format!("sk${}_{}", function.name(), i),
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
