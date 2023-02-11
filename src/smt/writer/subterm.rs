use std::{borrow::BorrowMut, cell::RefCell, collections::HashSet, ops::Deref};

use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT_NAME, SUBTERM},
            types::{BOOL, CONDITION, MSG, STEP},
        },
        env::Environement,
        formula::{sorts_to_variables, RichFormula, Variable},
        formula_iterator::{new_formula_iter_vec, FormulaIterator, IteratorFlags},
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::{cell::Assignement, problem::Problem, step::Step},
    smt::{
        macros::{sand, seq, sexists, sforall, sfun, simplies, sneq, snot, sor, svar},
        smt::{Smt, SmtFormula},
    },
    utils::utils::StackBox,
};
use bitflags::bitflags;
use if_chain::if_chain;

use super::Ctx;

bitflags! {
    #[derive(Default )]
    pub struct SubtermFlags: u8 {
        /// When used for side conditions, this lets you do away with all the `subterm input` & co
        const ALWAYS_PROCESSWIDE =      1 << 0;

    }
}
pub struct Subterm<B> {
    sort: Sort,
    name: String,
    flags: SubtermFlags,
    builder: B,
    inner: InnerSubterm,
}

enum InnerSubterm {
    Vmp {
        high_order_fun: Function,
        function: Function,
    },
    Base {
        sorts_order: Vec<Sort>,
        functions: Vec<Function>,
    },
}

impl<F> Subterm<F> {
    pub fn f(&self, a: SmtFormula, b: SmtFormula, sort: &Sort) -> SmtFormula {
        match &self.inner {
            InnerSubterm::Vmp {
                high_order_fun: sbt,
                function: f,
                ..
            } => sfun!(sbt; sfun!(f), a, b),
            InnerSubterm::Base {
                sorts_order,
                functions: f,
                ..
            } => {
                let i = sorts_order
                    .iter()
                    .position(|s| s == sort)
                    .unwrap_or_else(|| panic!("{:?}", sort));
                sfun!(f[i]; a, b)
            }
        }
    }

    pub fn name(&self) -> &String {
        &self.name
    }

    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    pub fn get_builder(&self) -> &F {
        &self.builder
    }
}

/// generate all the axioms for a subterm function
pub(crate) fn generate_subterm<'a, B>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &'a mut Ctx,
    name: &str,
    sort: &'a Sort,
    functions: Vec<&Function>,
    flags: SubtermFlags,
    builder: B,
) -> Subterm<B>
where
    // F: Fn(&Subterm, &SmtFormula, &Step, &'a Problem) -> SmtFormula,
    B: Builder<'a>,
{
    // assert!(ctx.env().no_subterm(), "trying to define a subterm even though they are deactivated");

    debug_assert!(ctx.pbl.env.verify_f());
    debug_assert!(
        functions.iter().all(|f| ctx.pbl.env.contains_f(f)),
        "\n\tfuns: {:?}\n\tf2: {:?}",
        &functions,
        ctx.pbl.env.get_functions_iter().collect_vec()
    );

    let subt = if ctx.pbl.env.use_special_subterm() {
        generate_special_subterm(
            assertions,
            declarations,
            ctx,
            name,
            sort,
            functions,
            flags,
            builder,
        )
    } else {
        generate_base_subterm(
            assertions,
            declarations,
            ctx,
            name,
            sort,
            functions,
            flags,
            builder,
        )
    };

    // if ctx.env().preprocessed_input() {
    if !subt.flags.contains(SubtermFlags::ALWAYS_PROCESSWIDE) {
        user_splitting(assertions, declarations, ctx, &subt);
    }
    // } else {
    // spliting(assertions, declarations, ctx, &subt /* .as_main() */);
    // spliting(assertions, declarations, ctx, subt.as_secondary());

    // for s in subt.iter() {
    //     spliting(assertions, declarations, ctx, s);
    // }
    // }
    subt
}

fn user_splitting<'a, B>(
    assertions: &mut Vec<Smt>,
    _: &mut Vec<Smt>,
    ctx: &'a mut Ctx,
    subt: &Subterm<B>,
) where
    B: Builder<'a>,
{
    // let preprocess = subt.get_builder();
    let input = INPUT(ctx.env());
    let lt = ctx.env().get_f(LT_NAME).unwrap();

    let flt = |s1: &SmtFormula, s2: &SmtFormula| sfun!(lt; s1.clone(), s2.clone());
    let flt_eq = |s1: &SmtFormula, s2: &SmtFormula| sor!(seq!(s1.clone(), s2.clone()), flt(s1, s2));

    let msg = MSG(ctx.env());
    // let cond = CONDITION(ctx.env());

    // biggest than any step variable
    let max_var = ctx.pbl.max_var();

    // make ununsed variables
    let sorts = vec![subt.sort().clone(), STEP(ctx.env()).clone()];
    let vars = sorts_to_variables(max_var, sorts.iter());
    let tp = svar!(vars[1].clone()); // a timepoint var
    let m = svar!(vars[0].clone()); // the message (or whatever other sort)

    let max_var = max_var + vars.len(); // update max_var

    // for reuse
    let todo = RefCell::new(Vec::new());

    {
        let mut ors = Vec::new();
        let input_f = sfun!(input; tp.clone());
        if subt.sort() == msg {
            ors.push(seq!(m.clone(), input_f.clone()))
        }
        user_spliting_inputs(ctx, &tp, &m, todo, &mut ors, subt, max_var, lt);
        assertions.push(Smt::Assert(SmtFormula::Forall(
            vars.clone(),
            Box::new(simplies!(ctx.env();
                subt.f(m.clone(), input_f, &msg),
                SmtFormula::Or(ors)
            )),
        )));
    }

    assertions.extend(
        ctx.pbl
            .memory_cells
            .values()
            .map(|c| {
                let c_vars = sorts_to_variables(max_var, c.args().iter());
                let max_var = max_var + c_vars.len();

                let smt_c = sfun!(
                    c.function(),
                    c_vars
                        .iter()
                        .map(SmtFormula::from)
                        .chain([tp.clone()].into_iter())
                        .collect()
                );

                let mut ors = if subt.sort() == msg {
                    vec![seq!(m.clone(), smt_c.clone())]
                } else {
                    vec![]
                };

                ors.extend(c.assignements().iter().map(
                    |Assignement {
                         step,
                         args,
                         content,
                     }| {
                        let eq_args = SmtFormula::And(
                            c_vars
                                .iter()
                                .map(SmtFormula::from)
                                .zip(args.iter().map(SmtFormula::from))
                                .map(|(a, b)| seq!(a, b))
                                .collect(),
                        );

                        // step <= tp
                        let order = {
                            let vars = step.free_variables().iter().map(SmtFormula::from).collect();
                            let step = sfun!(step.function(), vars);
                            flt_eq(&step, &tp)
                        };

                        let rec_call = subt.f(m.clone(), content.into(), msg);

                        let vars = step.occuring_variables().clone();
                        SmtFormula::Exists(vars, Box::new(sand!(order, eq_args, eq_args, rec_call)))
                    },
                ));

                let vars = vars.iter().cloned().chain(c_vars.into_iter()).collect();
                SmtFormula::Forall(
                    vars,
                    Box::new(simplies!(ctx.env();
                        subt.f(m.clone(), smt_c, msg),
                        SmtFormula::Or(ors)
                    )),
                )
            })
            .map(Smt::Assert),
    )
}

fn user_spliting_inputs<'a, B>(
    ctx: &'a Ctx,
    tp: &SmtFormula,
    m: &SmtFormula,
    todo: RefCell<Vec<&'a RichFormula>>,
    ors: &mut Vec<SmtFormula>,
    // preprocess: &F,
    subt: &Subterm<B>,
    max_var: usize,
    lt: &Function, // input: &Function,
                   // msg: &Sort,
) where
    B: Builder<'a>,
{
    let flt = |s1: &SmtFormula, s2: &SmtFormula| sfun!(lt; s1.clone(), s2.clone());
    let flt_eq = |s1: &SmtFormula, s2: &SmtFormula| sor!(seq!(s1.clone(), s2.clone()), flt(s1, s2));

    let mut calls_to_cells = Vec::new();
    ors.reserve(ctx.pbl.steps.len());
    for s in ctx.pbl.steps.values() {
        let s_vars = s.occuring_variables().clone();

        let step_f = sfun!(
            s.function(),
            s.free_variables()
                .iter()
                .cloned()
                .map(|v| svar!(v))
                .collect()
        );
        // step < tp
        let order = flt(&step_f, tp);

        let content = {
            let mut todo = todo.borrow_mut();
            todo.clear();

            todo.push(s.message());
            todo.push(s.condition());

            new_formula_iter_vec(todo, &ctx.pbl, IteratorFlags::QUANTIFIER, |f, p| {
                if_chain! {
                    if let RichFormula::Fun(fun, args) = f;
                    if fun.is_cell();
                    then {
                        calls_to_cells.push((s, fun, args))
                    }
                };
                subt.get_builder().preprocess(subt, m, s, p, f)
            })
            .collect_vec()
        }; // todo's RefMut dies here
        let r = SmtFormula::Exists(
            s_vars,
            Box::new(SmtFormula::And(vec![order, SmtFormula::Or(content)])),
        );
        ors.push(r);
    }

    let cells = calls_to_cells
        .iter()
        .map(|(_, fun, _)| {
            ctx.pbl
                .memory_cells
                .values()
                .find(|c| c.function() == *fun)
                .unwrap()
        })
        .collect_vec();

    ors.reserve(cells.iter().map(|c| c.assignements().len()).sum());
    for (cell, (s, fun, c_args)) in cells.into_iter().zip(calls_to_cells.into_iter()) {
        // c_args with its variables names moved away
        let c_args = c_args
            .iter()
            .map(|f| f.translate_vars(max_var))
            .collect_vec();
        // variables of the arguments of s
        let vars_s = s
            .free_variables()
            .iter()
            .cloned()
            .map(|v| Variable {
                id: v.id + max_var,
                ..v
            })
            .collect_vec();
        // s as an SmtFormula
        let s_smt = {
            let smt_vars_s = vars_s.iter().cloned().map(|v| svar!(v)).collect();
            sfun!(s.function(), smt_vars_s)
        };
        // s < tp
        let order_s = flt(&s_smt, tp);

        for Assignement {
            step,
            args,
            content,
        } in cell.assignements()
        {
            // should never fail, but we never know
            assert_eq!(args.len() + 1, c_args.len());

            // how the arguments map to one another
            let args_eq = SmtFormula::And(
                args.iter()
                    .zip(c_args.iter())
                    .map(|(a, b)| (SmtFormula::from(a), SmtFormula::from(b)))
                    .map(|(a, b)| seq!(a, b))
                    .collect(),
            );

            let inner_ors = {
                let mut todo = todo.borrow_mut();
                todo.clear();
                todo.push(content);
                new_formula_iter_vec(todo, &ctx.pbl, IteratorFlags::QUANTIFIER, |f, p| {
                    subt.get_builder().preprocess(subt, m, s, p, f)
                })
                .collect_vec()
            }; // todo's RefMut dies here

            // step <= s
            let order_step = {
                let vars = step
                    .free_variables()
                    .iter()
                    .cloned()
                    .map(SmtFormula::from)
                    .collect();
                let step_smt = sfun!(step.function(), vars);
                flt_eq(&step_smt, &s_smt)
            };
            // the content itself
            let content = sand!(order_s, order_step, args_eq, SmtFormula::Or(inner_ors));

            let r = SmtFormula::Exists(
                vars_s
                    .iter()
                    .cloned()
                    .chain(s.occuring_variables().iter().cloned())
                    .collect(),
                Box::new(content),
            );
            ors.push(r)
        }
    }
}

fn generate_comute_fun_vec<F>(
    env: &Environement,
    functions: Vec<&Function>,
    subt: &Subterm<F>,
) -> Vec<Function> {
    let b = subt.flags.contains(SubtermFlags::ALWAYS_PROCESSWIDE);
    env.get_functions_iter()
        .filter(|&f| {
            f.is_term_algebra()
                && (b || !f.is_special_subterm())
                && !functions.contains(&f)
                && !f.is_from_step()
        })
        .cloned()
        .collect()
}

fn generate_special_subterm<F>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
    flags: SubtermFlags,
    builder: F,
) -> Subterm<F> {
    let bool = BOOL(ctx.env());

    let input = INPUT(ctx.env()).clone();
    let f_main = Function::new_with_flag(name, vec![], bool.clone(), FFlags::SUBTERM_FUN);

    let step_sort = &STEP(ctx.env()).clone();

    assert!(ctx.env_mut().add_f(f_main.clone()));

    let subt = Subterm {
        sort: sort.clone(),
        name: name.to_owned(),
        flags,
        builder,
        inner: InnerSubterm::Vmp {
            high_order_fun: SUBTERM(ctx.env()).clone(),
            function: f_main.clone(),
        },
    };

    let funs_main = generate_comute_fun_vec(ctx.env(), functions, &subt);

    declarations.push(Smt::DeclareSubtermRelation(f_main, funs_main.clone()));

    let known_ta = [MSG(ctx.env()).clone(), CONDITION(ctx.env()).clone()];

    for s in ctx.env().get_sort_iter().filter(|&s| {
        (s != sort)
            && !if ctx.env().no_ta() {
                known_ta.contains(s)
            } else {
                s.is_term_algebra()
            }
            && (s != step_sort)
    }) {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.f(m, m2, s))}),
        ));
    }
    if sort.is_term_algebra() {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort; {subt.f(m.clone(), m, sort)}),
        ));
    } else {
        {
            let s = &subt;
            assertions.push(Smt::Assert(sforall!(m!1:sort, m2!2:sort; {
                simplies!(ctx.env();
                    s.f(m.clone(), m2.clone(), sort),
                    seq!(m, m2)
                )
            })))
        }
    }

    subt
}

fn generate_base_subterm<F>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
    flags: SubtermFlags,
    builder: F,
) -> Subterm<F> {
    let bool = BOOL(ctx.env()).clone();
    let input = INPUT(ctx.env()).clone();
    let step_sort = &STEP(ctx.env()).clone();

    let sorts = ctx
        .env()
        .get_sort_iter()
        .cloned()
        // .filter(Sort::is_term_algebra)
        .collect_vec();
    let subt_functions = sorts
        .iter()
        .map(|s| {
            let main = Function::new_with_flag(
                &format!("s$subterm_{}_{}", name, s.name()),
                vec![sort.clone(), s.clone()],
                bool.clone(),
                FFlags::empty(),
            );
            assert!(ctx.env_mut().add_f(main.clone()));

            main
        })
        .collect_vec();

    // declare all functions
    {
        declarations.extend(subt_functions.iter().cloned().map(|f| Smt::DeclareFun(f)))
    }

    let subterm = Subterm {
        sort: sort.clone(),
        name: name.to_owned(),
        flags,
        builder,
        inner: InnerSubterm::Base {
            sorts_order: sorts,
            functions: subt_functions,
        },
    };

    // functions on which the subterm commutes "blindly"
    let funs_main = generate_comute_fun_vec(ctx.env(), functions, &subterm);

    // prepare space for all the assertions
    assertions.reserve(2 * funs_main.len() + 1);

    // add the assertions
    {
        let iter = funs_main.iter().flat_map(|f| {
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
                let s = &subterm;
                [or_formulas.clone(), or_formulas]
                    .into_iter()
                    .map(|mut or_formulas| {
                        or_formulas.extend(
                            vars.iter()
                                .skip(1)
                                .map(|v| s.f(svar!(x.clone()), svar!(v.clone()), &v.sort)),
                        );

                        simplies!(ctx.env();
                            s.f(svar!(x.clone()), applied_f.clone(), &f.get_output_sort()),
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

    if let InnerSubterm::Base { sorts_order, .. } = &subterm.inner {
        let known_ta = [MSG(ctx.env()).clone(), CONDITION(ctx.env()).clone()];
        assertions.extend(
            sorts_order
                .iter()
                .filter(|&s| {
                    !if ctx.env().no_ta() {
                        known_ta.contains(s)
                    } else {
                        s.is_term_algebra()
                    } && (s != sort)
                        && (s != step_sort)
                })
                .map(|s| sforall!(x!1:sort, n!2:s; {snot!(ctx.env(); subterm.f(x, n, s))}))
                .map(|f| Smt::Assert(f)),
        )
    } else {
        unreachable!()
    }

    if sort.is_term_algebra() {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort; {subterm.f(m.clone(), m, sort)}),
        ))
    } else {
        assertions.push(Smt::Assert(sforall!(m!1:sort, m2!2:sort; {
            simplies!(ctx.env();
                subterm.f(m.clone(), m2.clone(), sort),
                seq!(m, m2)
            )
        })))
    }

    subterm
}

impl<'a, F> Subterm<F>
where
    F: Fn(
        &Subterm<F>,
        &SmtFormula,
        &Step,
        &'a Problem,
        &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>),
{
    /// I'm using the negative to avoid too many existential quantifiers
    pub(crate) fn generate_not_subterm_protocol(
        &self,
        assertions: &mut Vec<Smt>,
        declarations: &mut Vec<Smt>,
        ctx: &mut Ctx,
    ) -> Function {
        struct Aux<'a> {
            pbl: &'a Problem,
            var_set: HashSet<usize>,
            pile: Vec<&'a RichFormula>,
        }
        impl<'a> Aux<'a> {
            fn run(&mut self, f: &'a RichFormula) -> Vec<Variable> {
                self.var_set.clear();
                self.pile.clear();

                f.used_variables_iter_with_pile(&self.pbl, &mut self.pile)
                    .into_iter()
                    .filter(|v| self.var_set.insert(v.id))
                    .cloned()
                    .collect_vec()
            }
        }

        let bool = BOOL(ctx.env()).clone();
        let fun = ctx.env_mut().create_and_add_function(
            &format!("not_protocol${}", self.name()),
            &[self.sort()],
            &bool,
            FFlags::default(),
        );
        declarations.push(Smt::DeclareFun(fun.clone()));

        let max_var = ctx.pbl.max_var();
        let m_var = Variable {
            id: max_var,
            sort: self.sort().clone(),
        };
        let m = svar!(m_var.clone());

        let pile = {
            let from_steps = ctx
                .pbl
                .steps
                .values()
                .flat_map(|s| [s.message(), s.condition()]);
            let from_cells = ctx
                .pbl
                .memory_cells
                .values()
                .flat_map(|c| c.assignements().iter().map(|a| &a.content));

            from_steps.chain(from_cells).collect_vec()
        };

        let mut iter = FormulaIterator::new(
            StackBox::new(pile),
            &ctx.pbl,
            IteratorFlags::QUANTIFIER,
            |f, _| {
                (
                    Some(f),
                    match f {
                        RichFormula::Fun(_, args) => Some(args.iter()),
                        _ => None,
                    }
                    .into_iter()
                    .flatten(),
                )
            },
        );

        let mut f_set = HashSet::new();
        let mut get_vars = {
            Aux {
                pbl: &ctx.pbl,
                var_set: HashSet::new(),
                pile: Vec::new(),
            }
        };

        let ands = iter
            .filter(|&f| &f.get_sort(ctx.env()) == self.sort() && f_set.insert(f))
            .map(|f| {
                let vars = get_vars.run(f);
                SmtFormula::Forall(vars, Box::new(sneq!(m.clone(), SmtFormula::from(f))))
            })
            .collect_vec();

        assertions.push(Smt::Assert(SmtFormula::Forall(
            vec![m_var],
            Box::new(simplies!(ctx.env(); sfun!(fun; m), SmtFormula::And(ands))),
        )));

        fun
    }
}

pub trait Builder<'a> {
    fn preprocess(
        self,
        subt: &Subterm<Self>,
        m: &SmtFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized;
}

impl<'a, F> Builder<'a> for F
where
    F: Fn(
        &Subterm<F>,
        &SmtFormula,
        &Step,
        &'a Problem,
        &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>),
{
    fn preprocess(
        self,
        subt: &Subterm<Self>,
        m: &SmtFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized,
    {
        (self)(subt, m, s, pbl, f)
    }
}

pub struct DefaultBuilder();
impl<'a> Builder<'a> for DefaultBuilder {
    fn preprocess(
        self,
        subt: &Subterm<Self>,
        m: &SmtFormula,
        s: &Step,
        pbl: &'a Problem,
        f: &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>)
    where
        Self: Sized,
    {
        let sort = subt.sort();
        match f {
            RichFormula::Fun(fun, args) => (
                (&fun.get_output_sort() == sort).then(|| seq!(m.clone(), SmtFormula::from(f))),
                args.iter().collect(),
            ),
            RichFormula::Var(v) if &v.sort == sort => {
                (Some(seq!(m.clone(), svar!(v.clone()))), vec![])
            }
            _ => (None, vec![]),
        }
    }
}
