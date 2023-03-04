use std::{cell::RefCell, collections::HashSet, rc::Rc};

use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT_NAME},
            types::{BOOL, MSG, STEP},
        },
        formula::{sorts_to_variables, RichFormula, Variable},
        formula_iterator::{new_formula_iter_vec, IteratorFlags},
        formula_user::FormulaUser,
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::{cell::Assignement, problem::Problem},
    smt::{
        macros::*,
        smt::{Smt, SmtFormula},
        writer::Ctx,
    },
    utils::utils::{reset_vec, StackBox},
};

use super::{builder::Builder, Subterm};

use itertools::Itertools;

/// preprocess input and memory cells
pub(crate) fn preprocess<B>(assertions: &mut Vec<Smt>, _: &mut Vec<Smt>, ctx: &mut Ctx, subt: &Subterm<B>)
where
    B: Builder,
{
    // let preprocess = subt.get_builder();
    let input = INPUT(ctx.env());
    let lt = ctx.env().get_f(LT_NAME).unwrap();

    let flt = |s1: &SmtFormula, s2: &SmtFormula| sfun!(lt; s1.clone(), s2.clone());
    let _flt_eq =
        |s1: &SmtFormula, s2: &SmtFormula| sor!(seq!(s1.clone(), s2.clone()), flt(s1, s2));

    let msg = MSG(ctx.env());
    // let cond = CONDITION(ctx.env());

    // biggest than any step variable
    let max_var = ctx.pbl.max_var();

    // make ununsed variables
    let sorts = vec![subt.sort().clone(), STEP(ctx.env()).clone()];
    let vars = sorts_to_variables(max_var, sorts.iter());
    // let tp = svar!(vars[1].clone()); // a timepoint var
    // let m = svar!(vars[0].clone()); // the message (or whatever other sort)
    let m = &vars[0];
    let tp = &vars[1];

    let max_var = max_var + vars.len(); // update max_var

    let lt = Mlt { fun: lt.clone() };

    inputs(assertions, ctx, subt, tp, m, max_var, msg, &lt, input);
    memory_cells(assertions, ctx, max_var, subt, msg, &lt, tp, m);

    // {
    //     // input
    //     let mut ors = Vec::new();
    //     let input_f = sfun!(input; tp.clone());
    //     if subt.sort() == msg {
    //         ors.push(seq!(m.clone(), input_f.clone()))
    //     }
    //     inputs(ctx, &tp, &m, todo, &mut ors, subt, max_var, lt);
    //     assertions.push(Smt::Assert(SmtFormula::Forall(
    //         vars.clone(),
    //         Box::new(simplies!(ctx.env();
    //             subt.f(m.clone(), input_f, &msg),
    //             SmtFormula::Or(ors)
    //         )),
    //     )));
    // }

    // // memory cells
    // memory_cells(assertions, ctx, max_var, subt, msg, lt, tp, m);
}

/// preprocess memory cells
fn memory_cells<B>(
    assertions: &mut Vec<Smt>,
    ctx: &Ctx,
    max_var: usize,
    subt: &Subterm<B>,
    msg: &Sort,
    lt: &Mlt,
    tp: &Variable,
    m: &Variable,
    // vars: Vec<Variable>,
) where
    B: Builder,
{
    // let flt = |s1: &RichFormula, s2: &RichFormula| ctx.funf(lt.clone(), [s1.clone(), s2.clone()]);
    // let flt_eq =
    //     |s1: &RichFormula, s2: &RichFormula| ctx.orf(ctx.eqf(s1.clone(), s2.clone()), flt(s1, s2));
    assertions.extend(
        ctx.pbl
            .memory_cells
            .values()
            .map(|c| {
                let cell_vars = sorts_to_variables(max_var, c.args().iter());
                let _max_var = max_var + cell_vars.len();

                let smt_c: RichFormula = ctx.funf(
                    c.function().clone(),
                    cell_vars
                        .iter()
                        .chain([tp].into_iter())
                        .cloned()
                        .map(|v| ctx.varf(v))
                        .collect_vec(),
                );

                // let mut ors = if subt.sort() == msg {
                //     // vec![seq!(m.clone(), smt_c.clone())]
                //     vec![ctx.eqf(m.clone(), smt_c.clone())]
                // } else {
                //     vec![]
                // };

                let ors = c.assignements().iter().map(
                    |Assignement {
                         step,
                         args,
                         content,
                     }| {
                        let eq_args = ctx.mandf(
                            cell_vars
                                .iter()
                                // .map(SmtFormula::from)
                                .zip(args.iter() /* .map(SmtFormula::from) */)
                                .map(|(a, b)| ctx.eqf(a.clone_to_formula(ctx), b.clone())),
                        );

                        // step <= tp
                        let order = {
                            let vars = step
                                .free_variables()
                                .iter()
                                .map(|v| v.clone_to_formula(ctx));
                            let step = ctx.funf(step.function().clone(), vars);
                            // flt_eq(&step, &tp)
                            lt.leq(ctx, step, tp.clone_to_formula(ctx))
                        };

                        // will terminate because no loops
                        let rec_call = subt.f(ctx, m.clone_to_formula(ctx), content.clone(), msg);

                        let vars = step.occuring_variables().clone();
                        // SmtFormula::Exists(vars, Box::new(sand!(order, eq_args, eq_args, rec_call)))
                        ctx.existsf(vars, ctx.mandf([order, eq_args, rec_call]))
                    },
                );

                let vars = [m, tp]
                    .into_iter()
                    .chain(cell_vars.iter())
                    .cloned()
                    .collect();
                // SmtFormula::Forall(
                //     vars,
                //     Box::new(simplies!(ctx.env();
                //         subt.f(m.clone(), smt_c, msg),
                //         SmtFormula::Or(ors)
                //     )),
                // )
                ctx.forallf(
                    vars,
                    ctx.impliesf(
                        subt.f(ctx, m.clone_to_formula(ctx), smt_c.clone(), msg),
                        if subt.sort() == msg {
                            ctx.morf(
                                [ctx.eqf(m.clone_to_formula(ctx), smt_c)]
                                    .into_iter()
                                    .chain(ors),
                            )
                        } else {
                            ctx.morf(ors)
                        },
                    ),
                )
            })
            .map(SmtFormula::from)
            .map(Smt::Assert),
    )
}

/// Mutates `assertions` and/or `declaration` to add any relevant axioms
/// to encode `t \sqsubseteq \mathsf{input}(T)`
fn inputs<B>(
    // declarations: &mut Vec<Smt>,
    assertions: &mut Vec<Smt>,
    ctx: &Ctx,
    subt: &Subterm<B>,
    tp: &Variable,
    m: &Variable,
    // vars: &Vec<Variable>,
    _max_var: usize,
    msg: &Sort,
    lt: &Mlt,
    input: &Function,
) where
    B: Builder,
{
    // let flt = |s1: &RichFormula, s2: &RichFormula| ctx.funf(lt.clone(), [s1.clone(), s2.clone()]);
    // let flt_eq =
    //     |s1: &RichFormula, s2: &RichFormula| ctx.orf(ctx.eqf(s1.clone(), s2.clone()), flt(s1, s2));

    let pile = RefCell::new(Vec::new());
    let mut ors: Vec<RichFormula> = Vec::new();
    let premise;

    {
        let m: RichFormula = m.clone_to_formula(ctx);
        let tp: RichFormula = tp.clone_to_formula(ctx);
        let input = ctx.funf(input.clone(), [tp]);
        // m = input
        if subt.sort() == msg {
            ors.push(ctx.eqf(m.clone(), input.clone()))
        }

        premise = subt.f(ctx, m, input, msg)
    };

    // let cell_evidences = Vec::new(); // cell don't recurse, so we can skip this for now
    {
        for s in ctx.pbl.steps.values() {
            let step_vars = s.occuring_variables().clone();
            let step_formula = s.as_formula(ctx);

            let inner_ors = {
                let m = m.clone_to_formula(ctx);
                let mut pile = pile.borrow_mut();
                // let pile = reset_vec(pile.as_mut());
                pile.clear();
                pile.extend([s.message(), s.condition()]);
                let iter =
                    new_formula_iter_vec(pile, &ctx.pbl, IteratorFlags::QUANTIFIER, |f, pbl| {
                        // if_chain! {
                        //     if let RichFormula::Fun(fun, args) = f;
                        //     if fun.is_cell();
                        //     then {
                        //         cell_evidences.push((s, fun, args))
                        //     }
                        // }; cells don't recurse
                        subt.analyse(&m, Some(s), pbl, f)
                    });
                iter.collect_vec()
            };

            ors.push(ctx.existsf(
                step_vars,
                ctx.andf(
                    lt.lt(ctx, step_formula, tp.clone_to_formula(ctx)),
                    ctx.morf(inner_ors),
                ),
            ))
        }
    }
    assertions.push(Smt::Assert(SmtFormula::from(ctx.forallf(
        vec![m.clone(), tp.clone()],
        ctx.impliesf(premise, ctx.morf(ors)),
    ))))
}

/// I'm using the negative to avoid too many existential quantifiers
///
/// This returns a function `f: (t:self.sort()) -> Bool` saying that `t` never appears in the protocol
pub fn not_subterm_protocol<'a, B>(
    subt: &Subterm<B>,
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
) -> Function
where
    B: Builder,
{
    struct Aux<'a> {
        pbl: &'a Problem,
        var_set: HashSet<usize>,
        pile: Vec<*const RichFormula>,
    }
    impl<'a> Aux<'a> {
        fn run(&mut self, f: Rc<RichFormula>) -> Vec<Variable> {
            self.var_set.clear();
            let pile = reset_vec(&mut self.pile);

            f.used_variables_iter_with_pile(&self.pbl, pile)
                .into_iter()
                .filter(|v| self.var_set.insert(v.id))
                .cloned()
                .collect_vec()
        }
    }

    let bool = BOOL(ctx.env()).clone();
    let fun = ctx.env_mut().create_and_add_function(
        &format!("not_protocol${}", subt.name()),
        &[subt.sort()],
        &bool,
        FFlags::default(),
    );
    declarations.push(Smt::DeclareFun(fun.clone()));

    let max_var = ctx.pbl.max_var();
    let m = Variable {
        id: max_var,
        sort: subt.sort().clone(),
    };
    // let m = m_var.clone_to_formula(ctx);

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

    let iter = new_formula_iter_vec(
        StackBox::new(pile),
        &ctx.pbl,
        IteratorFlags::QUANTIFIER,
        |f, pbl| {
            // (
            //     Some(f),
            //     match f {
            //         RichFormula::Fun(_, args) => Some(args.iter()),
            //         _ => None,
            //     }
            //     .into_iter()
            //     .flatten(),
            // )
            // subt.builder().analyse(subt, m, s, pbl, f)
            let (f, next) = subt.analyse(&m.clone_to_formula(ctx), None, pbl, f);
            (f.map(|f| ctx.negf(f)), next)
        },
    );

    let mut f_set = HashSet::new();
    // let mut get_vars = {
    //     Aux {
    //         pbl: &ctx.pbl,
    //         var_set: HashSet::new(),
    //         pile: Vec::new(),
    //     }
    // };

    let ands = iter
        .map(|f| Rc::new(f))
        .filter(|f| &f.get_sort(ctx.env()) == subt.sort() && f_set.insert(Rc::clone(f)))
        .map(|f| (*f).clone())
        // .map(|f| {
        //     let vars = get_vars.run(Rc::clone(&f));
        //     // SmtFormula::Forall(vars, Box::new(sneq!(m.clone(), SmtFormula::from(f))))
        //     // ctx.forallf(vars, ctx.neqf(m.clone_to_formula(ctx), (*f).clone()))
        // })
        ;

    // assertions.push(Smt::Assert(SmtFormula::Forall(
    //     vec![m_var],
    //     Box::new(simplies!(ctx.env(); sfun!(fun; m), SmtFormula::And(ands))),
    // )));
    assertions.push(Smt::Assert(SmtFormula::from(
        ctx.forallf(vec![m.clone()], ctx.mandf(ands)),
    )));

    fun
}

struct Mlt {
    fun: Function,
}

impl Mlt {
    fn lt<T, U>(&self, ctx: &T, a: U, b: U) -> U
    where
        T: FormulaUser<U>,
    {
        ctx.funf(self.fun.clone(), [a, b])
    }

    fn leq<T, U>(&self, ctx: &T, a: U, b: U) -> U
    where
        T: FormulaUser<U>,
        U: Clone,
    {
        ctx.orf(ctx.eqf(a.clone(), b.clone()), self.lt(ctx, a, b))
    }
}