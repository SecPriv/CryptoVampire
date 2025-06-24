use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::INPUT,
            types::{BOOL, CONDITION, MSG, STEP},
        },
        formula::Variable,
    },
    smt::{
        macros::{seq, sforall, sfun, simplies, snot, svar},
        smt::{Smt, SmtFormula},
        writer::Ctx,
    },
};

use super::{InnerSubterm, Subterm, builder::Builder, preprocessing};

pub fn declare_and_base<'a, B>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    subt: &Subterm<B>,
) where
    B: Builder,
{
    match subt.kind() {
        super::SubtermKind::Vampire => {
            declare_and_base_vampire(assertions, declarations, ctx, subt)
        }
        super::SubtermKind::SmtCompliant => {
            declare_and_base_smtlib(assertions, declarations, ctx, subt)
        }
    }

    preprocessing::preprocess(assertions, declarations, ctx, subt);
}

pub fn declare_and_base_vampire<'a, B>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    subt: &Subterm<B>,
) {
    let _bool = BOOL(ctx.env());
    let _input = INPUT(ctx.env()).clone();
    let step_sort = STEP(ctx.env()).clone();

    if let Subterm {
        sort,
        // name,
        // flags,
        // ignored_functions,
        inner: InnerSubterm::Vampire { function, .. },
        ..
    } = subt
    {
        {
            // declare the function
            let funs_main = subt.commuting_functions(ctx.env()).cloned().collect();
            declarations.push(Smt::DeclareSubtermRelation(function.clone(), funs_main))
        }

        let known_ta = [MSG(ctx.env()).clone(), CONDITION(ctx.env()).clone()];

        assertions.extend(
            ctx.env()
                .get_sort_iter()
                .filter(|&s| {
                    (s != sort)
                        && !if ctx.env().no_ta() {
                            known_ta.contains(s)
                        } else {
                            s.is_term_algebra()
                        }
                        && (s != &step_sort)
                })
                .map(|s| sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.f(ctx, m, m2, s))}))
                .map(Smt::Assert),
        );

        if sort.is_term_algebra() {
            assertions.push(Smt::Assert(
                sforall!(m!1:sort; {subt.f(ctx, m.clone(), m, sort)}),
            ));
        } else {
            assertions.push(Smt::Assert(sforall!(m!1:sort, m2!2:sort; {
                simplies!(ctx.env();
                    subt.f(ctx, m.clone(), m2.clone(), sort),
                    seq!(m, m2)
                )
            })))
        }
    }
}

pub fn declare_and_base_smtlib<'a, B>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    subt: &Subterm<B>,
) {
    let step_sort = STEP(ctx.env()).clone();

    if let Subterm {
        sort,
        // name,
        // flags,
        // ignored_functions,
        inner:
            InnerSubterm::SmtCompliant {
                // sorts_order,
                functions,
                ..
            },
        ..
    } = subt
    {
        {
            // declare all functions
            declarations.extend(functions.iter().cloned().map(|f| Smt::DeclareFun(f)))
        }

        {
            let funs_main = subt.commuting_functions(ctx.env()).cloned();
            let iter = funs_main.flat_map(|f| {
                // the variables for the forall
                // the lhs var is first
                let vars = std::iter::once(sort.clone())
                    .chain(
                        f.input_sorts_iter()
                            // .filter(|s| s.is_term_algebra())
                            .map(|s| s.clone()),
                    )
                    .enumerate()
                    .map(|(id, s)| Variable::new(id, s))
                    .collect_vec();
                // the lhs var
                let x = vars.first().unwrap();

                // f(vars)
                // stored here to avoid repeating code
                let applied_f = sfun!(
                    f,
                    vars.iter().skip(1).map(|v| svar!(v.clone())).collect_vec()
                );

                // the content of the disjonction
                let mut or_formulas = Vec::with_capacity(vars.len());

                // no equality if it's useless
                if sort == &f.get_output_sort() {
                    or_formulas.push(seq!(svar!(x.clone()), applied_f.clone()))
                }

                {
                    let s = subt;
                    [or_formulas.clone(), or_formulas]
                        .into_iter()
                        .map(|mut or_formulas| {
                            or_formulas.extend(
                                vars.iter()
                                    .skip(1)
                                    .map(|v| s.f(ctx, svar!(x.clone()), svar!(v.clone()), &v.sort)),
                            );

                            simplies!(ctx.env();
                                s.f(ctx, svar!(x.clone()), applied_f.clone(), &f.get_output_sort()),
                                SmtFormula::Or(or_formulas)
                            )
                        })
                        .map(|f| Smt::Assert(SmtFormula::Forall(vars.clone(), Box::new(f))))
                        .collect_vec() // because it needs to take ownedship of vars
                        .into_iter()
                }
            });
            assertions.extend(iter);
        }

        {
            let known_ta = [MSG(ctx.env()).clone(), CONDITION(ctx.env()).clone()];
            assertions.extend(
                functions
                    .iter()
                    .map(|f| f.get_input_sorts().last().unwrap().clone())
                    .filter(|s| {
                        !if ctx.env().no_ta() {
                            known_ta.contains(s)
                        } else {
                            s.is_term_algebra()
                        } && (s != sort)
                            && (s != &step_sort)
                    })
                    .map(|s| sforall!(x!1:sort, n!2:s; {snot!(ctx.env(); subt.f(ctx, x, n, &s))}))
                    .map(|f| Smt::Assert(f)),
            )
        }

        if sort.is_term_algebra() {
            assertions.push(Smt::Assert(
                sforall!(m!1:sort; {subt.f(ctx, m.clone(), m, sort)}),
            ))
        } else {
            assertions.push(Smt::Assert(sforall!(m!1:sort, m2!2:sort; {
                simplies!(ctx.env();
                    subt.f(ctx, m.clone(), m2.clone(), sort),
                    seq!(m, m2)
                )
            })))
        }
    } else {
        unreachable!()
    }
}
