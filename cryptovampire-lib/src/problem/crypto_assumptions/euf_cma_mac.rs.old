use std::convert::identity;
use std::iter::repeat;
use std::rc::Rc;

use if_chain::if_chain;
use itertools::{Either, Itertools};

use crate::formula::builtins::functions::{BOOL_IF_THEN_ELSE, IF_THEN_ELSE, TRUE};
use crate::formula::formula_user::FormulaUser;
use crate::formula::sort::Sort;
use crate::formula::utils::Evaluator;

use crate::problem::cell::{Assignement, MemoryCell};
use crate::problem::cell_dependancies::graph::DependancyGraph;
use crate::problem::cell_dependancies::{CellCall, DependancyFromStep, OutGoingCall};
use crate::problem::crypto_assumptions::{DijBranch, Provenance};
use crate::problem::problem::Problem;
use crate::problem::step::Step;
use crate::smt::writer::subterm::builder::{Builder, DefaultBuilder};
use crate::smt::writer::subterm::preprocessing::{not_subterm_protocol, Mlt};
use crate::smt::writer::subterm::{Subterm, SubtermFlags};
use crate::utils::utils::transpose;
use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT, NONCE_MSG},
            types::{CONDITION, MSG, NONCE},
        },
        formula::{RichFormula, Variable},
        function::{FFlags, Function},
    },
    smt::{
        macros::{sand, seq, sexists, sforall, sfun, simplies, sor, srewrite, svar},
        smt::{RewriteKind, Smt, SmtFormula},
        writer::Ctx,
    },
};
pub(crate) fn generate<'pbl>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    mac: &Function,
    verify: &Function,
) {
    // let eval_msg = get_evaluate.msg(ctx,ctx.env());
    // let eval_cond = get_evaluate.cond(ctx,ctx.env());
    let evaluate = Evaluator::new(ctx.env()).unwrap();
    let nonce = NONCE_MSG(ctx.env()).clone();
    let msg = MSG(ctx.env()).clone();
    let cond = CONDITION(ctx.env()).clone();
    let nonce_sort = NONCE(ctx.env()).clone();
    let input_f = INPUT(ctx.env()).clone();
    let lt = LT(ctx.env()).clone();
    let graph = DependancyGraph::from(&ctx.pbl);
    let true_f = TRUE(ctx.env()).clone();

    let mtl = Mlt::new(lt.clone());

    // assertions.push(Smt::Assert(sforall!(sk!0:nonce_sort, m!1:msg; {
    //             sfun!(eval_cond; sfun!(verify; sfun!(mac; m.clone(), sfun!(nonce; sk.clone())), m.clone(),  sfun!(nonce; sk.clone())))
    //     })));
    assertions.push(Smt::Assert(ctx.forallff(
        [(0, &nonce_sort), (1, &msg)],
        |[sk, m]| {
            // ctx.funf(eval_cond.clone(), [ctx.funf(verify.clone(), [ctx.funf(mac.clone(), [m.clone(), ctx.funf(nonce.clone(), sk.clone())]), m.clone(), ctx.fun])])
            let nsk: SmtFormula = nonce.cf(ctx, [sk]);
            let mac = mac.cf(ctx, [m.clone(), nsk.clone()]);
            evaluate.cond(ctx, verify.cf(ctx, [mac, m, nsk]))
        },
    )));

    if ctx.env().preprocessing_plus() {
        preprocessing(
            ctx, verify, mac, input_f, graph, &nonce, &evaluate, true_f, mtl, assertions,
        );
    } else if !ctx.env().no_ta() {
        with_term_algebra(
            assertions,
            declarations,
            ctx,
            msg,
            nonce_sort,
            mac,
            verify,
            nonce,
            cond,
            &evaluate,
        );
    }
}

fn preprocessing(
    ctx: &Ctx,
    verify: &Function,
    mac: &Function,
    input_f: Function,
    graph: DependancyGraph,
    nonce: &Function,
    evaluate: &Evaluator,
    true_f: Function,
    mtl: Mlt,
    assertions: &mut Vec<Smt>,
) {
    // find candidates for preprocessing
    // verify(0, 1, nonce(2))
    let verify_candidates = ctx
        .pbl
        .iter_content()
        .map(|(_, f)| f)
        .chain(std::iter::once(&ctx.pbl.query))
        .chain(ctx.pbl.assertions.iter())
        .flat_map(|f| {
            f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                RichFormula::Fun(fun, args) if fun == verify => {
                    if_chain!(
                        if let RichFormula::Fun(f1, k) = &args[2];
                        if f1 == nonce;
                        if let RichFormula::Fun(_, _) = &k[0];
                        then {
                            (Some((&args[0], &args[1], &k[0])), vec![&args[0], &args[1]])
                        } else {
                            (None, args.iter().collect())
                        }
                    )
                }
                RichFormula::Fun(_, args) => (None, args.iter().collect()),
                _ => (None, vec![]),
            })
        })
        .unique();
    // .collect_vec();

    for (sigma, m, k) in verify_candidates
    /* .into_iter() */
    {
        // println!(
        //     "sigma = {}, m = {}, k = {}",
        //     SmtFormula::from(sigma),
        //     SmtFormula::from(m),
        //     SmtFormula::from(k)
        // );

        // side condtion on k
        let k_sc = key_side_condiction(k, ctx, sigma, m, verify, mac);

        if k_sc {
            // free vars of k
            // let fv = k.get_free_vars().into_iter().cloned().collect_vec();
            let fv = k
                .get_free_vars()
                .into_iter()
                .chain(m.get_free_vars().into_iter())
                .chain(sigma.get_free_vars().into_iter())
                .unique()
                .cloned()
                .collect_vec();

            // let max_var = fv
            //     .iter()
            //     .map(|v| v.id)
            //     // .chain(m.get_free_vars().iter().map(|v| v.id))
            //     .max()
            //     .unwrap_or(0);
            let max_var = ctx.pbl.max_var();

            // let u = Variable {
            //     id: max_var + 1,
            //     sort: msg.clone(),
            // };
            // let su = svar!(u.clone());
            // let max_var = max_var + 1;
            let sk = SmtFormula::from(k);
            let sm = SmtFormula::from(m);
            let ssigma = SmtFormula::from(sigma);

            #[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash)]
            enum InputOrCell<'pbl> {
                Input(&'pbl RichFormula),
                Cell(&'pbl MemoryCell, &'pbl RichFormula),
            }


            let (
                mut mac_candidates, // the hashes found in m and sigma (might be filtered out later)
                inputs_or_cells,    // the input(s) encountered
            ): (Vec<_>, Vec<_>) = [m, sigma]
                .into_iter()
                .flat_map(|f| {
                    f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                        RichFormula::Fun(fun, args) if fun == mac => (
                            Some(Either::Left(Provenance::Plain {
                                candidate: Candiate {
                                    m: &args[0],
                                    k: &args[1],
                                },
                            })),
                            args.iter().collect(),
                        ),
                        RichFormula::Fun(fun, args) if fun == &input_f => {
                            (Some(Either::Right(InputOrCell::Input(&args[0]))), vec![])
                        }
                        RichFormula::Fun(fun, args) if fun.is_cell() => {
                            assert!(args.last().is_some());
                            let cell = ctx.pbl.memory_cells.get(fun.name()).unwrap();
                            (
                                Some(Either::Right(InputOrCell::Cell(cell, args.last().unwrap()))),
                                vec![],
                            )
                        }
                        RichFormula::Fun(_, args) => (None, args.iter().collect()),
                        _ => (None, vec![]),
                    })
                })
                .partition_map(identity);

            let (inputs, cells): (Vec<_>, Vec<_>) =
                inputs_or_cells.into_iter().partition_map(|e| match e {
                    InputOrCell::Input(arg) => Either::Left(arg),
                    InputOrCell::Cell(cell, arg) => Either::Right((cell, arg)),
                });

            if !inputs.is_empty() {
                // if there were no inputs in m and sigma, no need to explore the whole protocol !
                find_candidates_input(&mut mac_candidates, ctx, mac, &graph);
            }

            find_candidantes_memory_cells(ctx, &mut mac_candidates, cells, mac, &graph);

            // let mut pile = RefCell::mew(vec![]);
            // mac_candidates.extend(cells.into_iter().flat_map(|(cell, call_t_args)| {
            //     graph.find_dependencies(Some(cell)).into_iter().
            // }));

            let inputs = inputs
                .into_iter()
                .unique()
                // .map(|f| SmtFormula::from(f))
                .collect_vec();

            let ors = {
                let branches = calculate_branches(
                    mac_candidates,
                    max_var,
                    ctx,
                    nonce,
                    k,
                    evaluate,
                    m,
                    &true_f,
                    inputs,
                    &mtl,
                );

                branches
                    .into_iter()
                    .map(
                        |DijBranch {
                             vars,
                             guard,
                             content,
                         }| {
                            ctx.existsf(vars, ctx.andf(*guard, *content))
                        },
                    )
                    .collect_vec()
            };

            assertions.push(Smt::Assert(SmtFormula::Forall(
                fv,
                Box::new(simplies!(ctx.env();
                    evaluate.cond(ctx, sfun!(verify;ssigma, sm.clone(), sfun!(nonce; sk.clone()))),
                    // SmtFormula::Exists(vec![u], Box::new(SmtFormula::Or(ors))))),
                    SmtFormula::Or(ors.into_iter().map(|f| f.into()).collect()))),
            )))
        }
    }
}

fn calculate_branches(
    mac_candidates: Vec<Provenance<Candiate>>,
    max_var: usize,
    ctx: &Ctx,
    nonce: &Function,
    k: &RichFormula,
    evaluate: &Evaluator,
    m: &RichFormula,
    true_f: &Function,
    inputs: Vec<&RichFormula>,
    mtl: &Mlt,
) -> Vec<DijBranch> {
    mac_candidates
        .into_iter()
        .map(|p| {
            let Candiate { m: m2, k: k2 } = p.candidate();
            let content_offset = max_var;
            let m2 = m2.translate_vars(max_var);
            let k2 = k2.translate_vars(max_var);
            let max_var = 2 * max_var;

            let content = ctx.mandf([
                ctx.eqf(nonce.cf(ctx, [k.clone()]), k2),
                ctx.eqf(evaluate.msg(ctx, m.clone()), evaluate.msg(ctx, m2)),
            ]);
            let content = Box::new(content);

            match p {
                Provenance::Plain { .. } => DijBranch {
                    vars: vec![],
                    guard: Box::new(true_f.cf(ctx, [])),
                    content,
                },
                Provenance::InputPlain { step, .. } => {
                    let (step_f, vars) = step_to_formula_and_vars(step, ctx, content_offset);

                    let guard = inputs
                        .iter()
                        .map(|t| mtl.lt(ctx, step_f.clone(), (*t).clone()));
                    let guard = Box::new(ctx.morf(guard));
                    DijBranch {
                        vars,
                        guard,
                        content,
                    }
                }
                Provenance::InputCell {
                    steps,
                    assgnm: Assignement { step, .. },
                    ..
                } => {
                    let (step_f, vars) = step_to_formula_and_vars(step, ctx, content_offset);

                    let guard = inputs.iter().cartesian_product(steps.iter()).map(|(t, s)| {
                        let vars = s
                            .free_variables()
                            .iter()
                            .cloned()
                            .map(|v| v + max_var)
                            .collect_vec();
                        let s_f: RichFormula = s
                            .function()
                            .cf(ctx, vars.iter().cloned().map(|v| v.as_formula(ctx)));
                        ctx.existsf(
                            vars,
                            ctx.mandf([
                                mtl.lt(ctx, s_f.clone(), (*t).clone()),
                                mtl.leq(ctx, step_f.clone(), s_f),
                            ]),
                        )
                    });
                    let guard = Box::new(ctx.morf(guard));
                    DijBranch {
                        vars,
                        guard,
                        content,
                    }
                }
                Provenance::CellPlain {
                    call_t_arg,
                    assgnm: Assignement { step, .. },
                    ..
                } => {
                    let (step_f, vars) = step_to_formula_and_vars(step, ctx, content_offset);

                    let guard = mtl.leq(ctx, step_f.clone(), call_t_arg.clone());
                    let guard = Box::new(guard);
                    DijBranch {
                        vars,
                        guard,
                        content,
                    }
                }
                Provenance::CellDeep {
                    steps,
                    call_t_arg,
                    assgnm: Assignement { step, .. },
                    ..
                } => {
                    let (step_f, vars) = step_to_formula_and_vars(step, ctx, content_offset);
                    let guard = steps.iter().map(|s| {
                        let vars = s
                            .free_variables()
                            .iter()
                            .cloned()
                            .map(|v| v + max_var)
                            .collect_vec();
                        let s_f: RichFormula = s
                            .function()
                            .cf(ctx, vars.iter().cloned().map(|v| v.as_formula(ctx)));
                        ctx.existsf(
                            vars,
                            ctx.mandf([
                                mtl.leq(ctx, s_f.clone(), call_t_arg.clone()),
                                mtl.leq(ctx, step_f.clone(), s_f),
                            ]),
                        )
                    });
                    let guard = Box::new(ctx.morf(guard));
                    DijBranch {
                        vars,
                        guard,
                        content,
                    }
                }
                Provenance::CellInput {
                    steps,
                    call_t_arg,
                    step,
                    ..
                } => {
                    let (step_f, vars) = step_to_formula_and_vars(step, ctx, content_offset);

                    let guard = steps.iter().map(|s| {
                        let vars = s
                            .free_variables()
                            .iter()
                            .cloned()
                            .map(|v| v + max_var)
                            .collect_vec();
                        let s_f: RichFormula = s
                            .function()
                            .cf(ctx, vars.iter().cloned().map(|v| v.as_formula(ctx)));
                        ctx.existsf(
                            vars,
                            ctx.mandf([
                                mtl.leq(ctx, s_f.clone(), call_t_arg.clone()),
                                mtl.lt(ctx, step_f.clone(), s_f),
                            ]),
                        )
                    });
                    let guard = Box::new(ctx.morf(guard));
                    DijBranch {
                        vars,
                        guard,
                        content,
                    }
                }
            }
        })
        .collect_vec()
}

fn step_to_formula_and_vars(
    step: &Step,
    ctx: &Ctx,
    content_offset: usize,
) -> (RichFormula, Vec<Variable>) {
    let step_f: RichFormula = step.function().cf(
        ctx,
        step.free_variables()
            .iter()
            .cloned()
            .map(|v| (v + content_offset).as_formula(ctx)),
    );
    let vars = step
        .occuring_variables()
        .iter()
        .cloned()
        .map(|v| v + content_offset)
        .collect();
    (step_f, vars)
}

fn key_side_condiction(
    k: &RichFormula,
    ctx: &Ctx,
    sigma: &RichFormula,
    m: &RichFormula,
    verify: &Function,
    mac: &Function,
) -> bool {
    let kfun = if let RichFormula::Fun(f, _) = k {
        f
    } else {
        unreachable!("{}", k)
        // continue;
    };
    let tmp = ctx
        .pbl
        .iter_content()
        .map(|(_, f)| f)
        .chain([sigma, m].into_iter())
        .flat_map(|f| {
            f.custom_iter_w_quantifier(&ctx.pbl, |f, _| match f {
                RichFormula::Fun(fun, _) if fun == kfun => (Some(()), vec![]),
                RichFormula::Fun(fun, args) if fun == verify || fun == mac => {
                    (None, args.iter().rev().skip(1).collect())
                }
                RichFormula::Fun(_, args) => (None, args.iter().collect()),
                _ => (None, vec![]),
            })
        })
        .next()
        .is_none();
    tmp
}

fn with_term_algebra(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    msg: Sort,
    nonce_sort: Sort,
    mac: &Function,
    verify: &Function,
    nonce: Function,
    cond: Sort,
    evaluate: &Evaluator,
) {
    let subt_main = Subterm::new_and_init(
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_main".to_owned(),
        msg.clone(),
        vec![],
        Default::default(),
        DefaultBuilder(),
    );
    let subt_sec = Subterm::new_and_init(
        assertions,
        declarations,
        ctx,
        "sbt$euf_hash_sec".to_owned(),
        nonce_sort.clone(),
        [mac.clone(), verify.clone()],
        SubtermFlags::ALWAYS_PROCESSWIDE,
        {
            struct MBuilder {
                nonce_sort: Sort,
                nonce: Function,
                verify: Function,
                mac: Function,
            }
            impl Builder for MBuilder {
                fn analyse<'pbl>(
                    &self,
                    _: &Subterm<Self>,
                    m: &RichFormula,
                    _: Option<&crate::problem::step::Step>,
                    pbl: &'pbl crate::problem::problem::Problem,
                    f: &'pbl RichFormula,
                ) -> (Option<RichFormula>, Vec<&'pbl RichFormula>)
                where
                    Self: Sized,
                {
                    let MBuilder {
                        nonce_sort,
                        nonce,
                        verify,
                        mac,
                    } = self;
                    match f {
                        RichFormula::Var(v) if v.sort() == nonce_sort => {
                            (Some(pbl.eqf(m.clone(), f.clone())), vec![])
                        }
                        RichFormula::Fun(fun, args) if fun == mac => {
                            let mut todo = Vec::with_capacity(2);
                            todo.push(&args[0]);
                            if_chain!(
                                if let RichFormula::Fun(fun2, _) = &args[1];
                                if fun2 == nonce;
                                then {}
                                else {
                                    todo.push(&args[1])
                                }
                            );
                            (None, todo)
                        }
                        RichFormula::Fun(fun, args) if fun == verify => {
                            let mut todo = Vec::with_capacity(3);
                            todo.push(&args[0]);
                            todo.push(&args[1]);
                            if_chain!(
                                if let RichFormula::Fun(fun2, _) = &args[2];
                                if fun2 == nonce;
                                then {}
                                else {
                                    todo.push(&args[2])
                                }
                            );
                            (None, todo)
                        }
                        RichFormula::Fun(fun, args) => (
                            (&fun.get_output_sort() == nonce_sort)
                                .then(|| pbl.eqf(m.clone(), f.clone())),
                            args.iter().collect(),
                        ),
                        _ => (None, vec![]),
                    }
                }
            }
            MBuilder {
                nonce_sort: nonce_sort.clone(),
                nonce: nonce.clone(),
                verify: verify.clone(),
                mac: mac.clone(),
            }
        },
    );

    // for s in subt_sec.iter() {
    //     assertions.push(Smt::Assert(sforall!(k!0:nonce_sort, m!1:msg, k2!2:msg; {
    //         simplies!(ctx.env();
    //             s.f(ctx, k.clone(), sfun!(mac; m.clone(), k2.clone()), &msg),
    //             site!(
    //                 seq!(k2.clone(), sfun!(nonce; k.clone())),
    //                 s.f(ctx, k.clone(), m.clone(), &msg),
    //                 sor!(
    //                     s.f(ctx, k.clone(), m.clone(), &msg),
    //                     s.f(ctx, k.clone(), k2.clone(), &msg)
    //                 )
    //             )
    //         )
    //     })));

    //     assertions.push(Smt::Assert(
    //         sforall!(k!0:nonce_sort, sigma!3:msg, m!1:msg, k2!2:msg; {
    //             simplies!(ctx.env();
    //                 s.f(ctx, k.clone(), sfun!(verify; m.clone(), sigma.clone(), k2.clone()), &cond),
    //                 site!(
    //                     seq!(k2.clone(), sfun!(nonce; k.clone())),
    //                     sor!(
    //                         s.f(ctx, k.clone(), m.clone(), &msg),
    //                         s.f(ctx, k.clone(), sigma.clone(), &msg)
    //                     ),
    //                     sor!(
    //                         s.f(ctx, k.clone(), m.clone(), &msg),
    //                         s.f(ctx, k.clone(), k2.clone(), &msg),
    //                         s.f(ctx, k.clone(), sigma.clone(), &msg)
    //                     )
    //                 )
    //             )
    //         }),
    //     ))
    // }
    assertions.extend(
        [
            ctx.forallff(
                [(0, &nonce_sort), (1, &msg), (2, &msg)],
                |[k, m, k2]: [SmtFormula; 3]| {
                    ctx.impliesf(
                        subt_sec.f(ctx, k.clone(), mac.cf(ctx, [m.clone(), k2.clone()]), &msg),
                        BOOL_IF_THEN_ELSE(ctx.env()).cf(
                            ctx,
                            [
                                ctx.eqf(k2.clone(), nonce.cf(ctx, [k.clone()])),
                                subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                                ctx.orf(
                                    subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                                    subt_sec.f(ctx, k.clone(), k2.clone(), &msg),
                                ),
                            ],
                        ),
                    )
                },
            ),
            ctx.forallff(
                [(0, &nonce_sort), (3, &msg), (1, &msg), (2, &msg)],
                |[k, sigma, m, k2]: [SmtFormula; 4]| {
                    ctx.impliesf(
                        subt_sec.f(
                            ctx,
                            k.clone(),
                            verify.cf(ctx, [m.clone(), sigma.clone(), k2.clone()]),
                            &cond,
                        ),
                        BOOL_IF_THEN_ELSE(ctx.env()).cf(
                            ctx,
                            [
                                ctx.eqf(k2.clone(), nonce.cf(ctx, [k.clone()])),
                                ctx.orf(
                                    subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                                    subt_sec.f(ctx, k.clone(), sigma.clone(), &msg),
                                ),
                                ctx.morf([
                                    subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                                    subt_sec.f(ctx, k.clone(), k2.clone(), &msg),
                                    subt_sec.f(ctx, k.clone(), sigma.clone(), &msg),
                                ]),
                            ],
                        ),
                    )
                },
            ),
        ]
        .into_iter()
        .map(Smt::Assert),
    );

    let not_protocol_wide_subterm = not_subterm_protocol(&subt_sec, assertions, declarations, ctx);

    if ctx.env().crypto_rewrite() {
        let sk = Function::new_with_flag(
            "sk$u$euf_cma",
            vec![msg.clone(), msg.clone(), nonce_sort.clone()],
            msg.clone(),
            FFlags::SKOLEM,
        );
        let asser = srewrite!(
                RewriteKind::Bool; s!1:msg, k!2:nonce_sort, m!3:msg;
                {
                    // seq!(
                    //     sfun!(eval_msg; s.clone()),
                    //     sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                    // )
                    evaluate.cond(ctx, sfun!(verify; s.clone(), m.clone(), sfun!(nonce; k.clone())))
                } -> {
                    let u = sfun!(sk; s.clone(), m.clone(), k.clone());
                    let h = sfun!(mac; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.f(ctx, h.clone(), s.clone(), &msg),
                            subt_main.f(ctx, h.clone(), m.clone(), &msg),
                            subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                            subt_sec.f(ctx, k.clone(), s.clone(), &msg),
                            ctx.negf(ctx.funf(not_protocol_wide_subterm, [k.clone()]))
                        ),
                        seq!(evaluate.msg(ctx, m.clone()), evaluate.msg(ctx, u.clone()))
                    )
                }
        );

        declarations.push(Smt::DeclareFun(sk));
        assertions.push(asser);
    } else {
        let asser = sforall!(s!1:msg, k!2:nonce_sort, m!3:msg;{
                simplies!(ctx.env();
                    // seq!(
                    //     sfun!(eval_msg; s.clone()),
                    //     sfun!(eval_msg; sfun!(hash; m.clone(), sfun!(nonce; k.clone())))
                    // )
                    sand!(
                        // sfun!(eval_cond; sfun!(verify; s.clone(), m.clone(), sfun!(nonce; k.clone()))),
                        evaluate.cond(ctx, verify.cf(ctx, [s.clone(), m.clone(), nonce.cf(ctx, [k.clone()])])),
                        not_protocol_wide_subterm.cf(ctx, [k.clone()])
                    )
                ,
                    sexists!(u!4:msg; {
                    let h = sfun!(mac; u.clone(), sfun!(nonce; k.clone()));
                    sand!(
                        sor!(
                            subt_main.f(ctx, h.clone(), s.clone(), &msg),
                            subt_main.f(ctx, h.clone(), m.clone(), &msg),
                            subt_sec.f(ctx, k.clone(), m.clone(), &msg),
                            subt_sec.f(ctx, k.clone(), s.clone(), &msg)
                        ),
                        seq!(evaluate.msg(ctx, m.clone()), evaluate.msg(ctx, u.clone()))
                    )})
                )}
        );
        assertions.push(Smt::Assert(asser));
    }
}

fn find_candidates_input<'pbl, 'b>(
    mac_candidates: &mut Vec<Provenance<'pbl, Candiate<'pbl>>>,
    ctx: &'pbl Ctx,
    mac: &'b Function,
    graph: &DependancyGraph<'pbl>,
) where
    'b: 'pbl,
{
    mac_candidates.extend(ctx.pbl.iter_content().flat_map(|(step, f)| {
        find_candidate(ctx, mac, f, |candidate| Provenance::InputPlain {
            step,
            candidate,
        })
    }));

    mac_candidates.extend({
        transpose(
            ctx.pbl
                .steps
                .values()
                .map(|step| (step, graph.find_dependencies_from_step(step)))
                .collect_vec(),
        )
        .into_iter()
        .flat_map(|(cell, steps)| {
            let steps: Rc<[_]> = steps.into();
            cell.assignements()
                .iter()
                .zip(std::iter::repeat((steps, cell)))
        })
        .flat_map(|(a @ Assignement { content, .. }, (steps, cell))| {
            find_candidate(ctx, mac, content, move |candidate| Provenance::InputCell {
                steps: Rc::clone(&steps),
                assgnm: a,
                candidate,
                cell,
            })
        })
    });
}

fn find_candidantes_memory_cells<'pbl, 'b>(
    ctx: &'pbl Ctx,
    mac_candidates: &mut Vec<Provenance<'pbl, Candiate<'pbl>>>,
    cells: Vec<(&'pbl MemoryCell, &'pbl RichFormula)>,
    mac: &'b Function,
    graph: &DependancyGraph<'pbl>,
) where
    'b: 'pbl,
{
    let ctx: &Ctx = ctx;
    mac_candidates.extend(cells.into_iter().flat_map(|(cell, call_t_arg)| {
        let plain = cell
            .assignements()
            .iter()
            .flat_map(|a @ Assignement { content, .. }| {
                find_candidate(ctx, mac, content, |candidate| Provenance::CellPlain {
                    call_t_arg,
                    assgnm: a,
                    candidate,
                    cell,
                })
            });
        let calll = Box::new(call_t_arg);
        let deeper = graph
            .find_dependencies_keep_steps(cell)
            .unwrap()
            .into_iter()
            .flat_map({
                // let call_t_arg = &call_t_arg;
                // let ctx = &ctx;
                move |DependancyFromStep { steps_origin, cell }| {
                    let steps: Rc<[_]> = steps_origin.into();
                    match cell {
                        None => {
                            let calll = calll.clone();
                            Either::Left(ctx.pbl.steps.values().flat_map(move |step| {
                                let steps = Rc::clone(&steps);
                                let calll = calll.clone();
                                [step.condition(), step.message()]
                                    .into_iter()
                                    .zip(repeat(steps))
                                    .flat_map(move |(f, steps)| {
                                        let steps = Rc::clone(&steps);
                                        let calll = calll.clone();
                                        find_candidate(ctx, mac, f, move |candidate| {
                                            Provenance::CellInput {
                                                steps: Rc::clone(&steps),
                                                call_t_arg: *calll,
                                                candidate,
                                                step,
                                            }
                                        })
                                    })
                            }))
                        }
                        Some(cell) => {
                            let steps = Rc::clone(&steps);
                            Either::Right(cell.assignements().iter().zip(repeat(steps)).flat_map({
                                let calll = calll.clone();
                                move |(a @ Assignement { content, .. }, steps)| {
                                    let calll = calll.clone();
                                    // let steps = Rc::clone(&steps);
                                    find_candidate(ctx, mac, content, move |candidate| {
                                        Provenance::CellDeep {
                                            steps: Rc::clone(&steps),
                                            call_t_arg: *calll,
                                            assgnm: a,
                                            candidate,
                                            cell,
                                        }
                                    })
                                }
                            }))
                        }
                    }
                }
            });

        plain.chain(deeper)
    }))
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Copy)]
struct Candiate<'pbl> {
    m: &'pbl RichFormula,
    k: &'pbl RichFormula,
}

fn find_candidate<'pbl, F, T>(
    ctx: &'pbl Ctx,
    mac: &'pbl Function,
    f: &'pbl RichFormula,
    function: F,
) -> impl Iterator<Item = T> + 'pbl
where
    F: Fn(Candiate<'pbl>) -> T + 'pbl,
    T: 'pbl,
{
    f.custom_iter_w_quantifier(&ctx.pbl, move |f, _| match f {
        RichFormula::Fun(fun, args) if fun == mac => {
            let candidate = Candiate {
                m: &args[0],
                k: &args[1],
            };
            (Some(function(candidate)), args.iter().collect())
        }
        RichFormula::Fun(_, args) => (None, args.iter().collect()),
        _ => (None, vec![]),
    })
}
