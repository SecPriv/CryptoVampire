use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT_NAME, SUBTERM},
            types::{BOOL, CONDITION, MSG, STEP},
        },
        env::Environement,
        formula::{sorts_to_variables, RichFormula, Variable},
        function::{FFlags, Function},
        sort::Sort,
    },
    problem::{problem::Problem, protocol::Step},
    smt::{
        macros::{sand, seq, sexists, sforall, sfun, simplies, snot, sor, svar},
        smt::{Smt, SmtFormula},
    },
};

use super::Ctx;

pub enum Subterm {
    VampireSpecial {
        sort: Sort,
        vampire_subterm_fun: Function,
        main: Function,
        secondary: Function,
    },
    Base {
        sort: Sort,
        sorts_order: Vec<Sort>,
        main: Vec<Function>,
        secondary: Vec<Function>,
        name: String,
    },
}

pub(crate) enum OneSubterm<'a> {
    Main(&'a Subterm),
    Secondary(&'a Subterm),
}

impl Subterm {
    pub fn main(&self, a: SmtFormula, b: SmtFormula, sort: &Sort) -> SmtFormula {
        match self {
            Subterm::VampireSpecial {
                vampire_subterm_fun: sbt,
                main: f,
                ..
            } => sfun!(sbt; sfun!(f), a, b),
            Subterm::Base {
                sorts_order,
                main: f,
                ..
            } => Self::call_base(sorts_order, f, a, b, sort),
        }
    }
    pub fn secondary(&self, a: SmtFormula, b: SmtFormula, sort: &Sort) -> SmtFormula {
        match self {
            Subterm::VampireSpecial {
                vampire_subterm_fun: sbt,
                secondary: f,
                ..
            } => sfun!(sbt; sfun!(f), a, b),
            Subterm::Base {
                sorts_order,
                secondary: f,
                ..
            } => Self::call_base(sorts_order, f, a, b, sort),
        }
    }

    fn call_base(
        sorts: &Vec<Sort>,
        f: &Vec<Function>,
        a: SmtFormula,
        b: SmtFormula,
        sort: &Sort,
    ) -> SmtFormula {
        let i = sorts
            .iter()
            .position(|s| s == sort)
            .unwrap_or_else(|| panic!("{:?}", sort));
        sfun!(f[i]; a, b)
    }

    pub fn name_main(&self) -> String {
        // self.as_tuple().0.name()
        match self {
            Subterm::VampireSpecial { main: f, .. } => f.name(),
            Subterm::Base { name, .. } => name,
        }
        .to_owned()
    }

    pub fn name_secondary(&self) -> String {
        match self {
            Subterm::VampireSpecial { secondary: f, .. } => f.name().to_owned(),
            Subterm::Base { name, .. } => name.to_owned() + "_bis",
        }
    }

    fn as_main<'a>(&'a self) -> OneSubterm<'a> {
        OneSubterm::Main(self)
    }

    fn as_secondary<'a>(&'a self) -> OneSubterm<'a> {
        OneSubterm::Secondary(self)
    }

    pub fn sort(&self) -> &Sort {
        match self {
            Subterm::VampireSpecial { sort, .. } => sort,
            Subterm::Base { sort: s, .. } => s,
        }
    }

    pub(crate) fn iter<'a>(&'a self) -> impl Iterator<Item = OneSubterm<'a>> {
        [self.as_main(), self.as_secondary()].into_iter()
    }
}

impl<'a> OneSubterm<'a> {
    pub fn f(&self, a: SmtFormula, b: SmtFormula, sort: &Sort) -> SmtFormula {
        match self {
            OneSubterm::Main(s) => s.main(a, b, sort),
            OneSubterm::Secondary(s) => s.secondary(a, b, sort),
        }
    }

    pub fn name(&self) -> String {
        match self {
            OneSubterm::Main(s) => s.name_main(),
            OneSubterm::Secondary(s) => s.name_secondary(),
        }
    }

    fn inner(&self) -> &'a Subterm {
        match self {
            OneSubterm::Main(s) => s,
            OneSubterm::Secondary(s) => s,
        }
    }

    pub fn sort(&self) -> &'a Sort {
        self.inner().sort()
    }
}

// type MyF<'a, 'b> = Fn(&Subterm, &SmtFormula, &Step, &'a Problem, &'b RichFormula) -> (SmtFormula, Vec<&'b RichFormula>);

pub(crate) fn generate_subterm<'a, F>(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &'a mut Ctx,
    name: &str,
    sort: &'a Sort,
    functions: Vec<&Function>,
    preprocess: F,
) -> Subterm
where
    // F: Fn(&Subterm, &SmtFormula, &Step, &'a Problem) -> SmtFormula,
    F: Fn(
        &Subterm,
        &SmtFormula,
        &Step,
        &'a Problem,
        &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>),
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
        generate_special_subterm(assertions, declarations, ctx, name, sort, functions)
    } else {
        generate_base_subterm(assertions, declarations, ctx, name, sort, functions)
    };

    if ctx.env().preprocessed_input() {
        user_splitting(assertions, declarations, ctx, &subt, preprocess)
    } else {
        spliting(assertions, declarations, ctx, &subt /* .as_main() */);
        // spliting(assertions, declarations, ctx, subt.as_secondary());

        // for s in subt.iter() {
        //     spliting(assertions, declarations, ctx, s);
        // }
    }
    subt
}

fn user_splitting<'a, F>(
    assertions: &mut Vec<Smt>,
    _: &mut Vec<Smt>,
    ctx: &'a mut Ctx,
    subt: &Subterm,
    preprocess: F,
) where
    F: Fn(
        &Subterm,
        &SmtFormula,
        &Step,
        &'a Problem,
        &'a RichFormula,
    ) -> (Option<SmtFormula>, Vec<&'a RichFormula>),
{
    let input = INPUT(ctx.env());
    let lt = ctx.env().get_f(LT_NAME).unwrap();
    let msg = MSG(ctx.env());
    // let cond = CONDITION(ctx.env());

    // biggest than any step variable
    let max_var = ctx
        .pbl
        .steps
        .values()
        .map(|s| s.vairable_range().end)
        .max()
        .unwrap_or(0);
    // make ununsed variables
    let sorts = vec![subt.sort().clone(), STEP(ctx.env()).clone()];
    let vars = sorts_to_variables(max_var, sorts.iter());
    let tp = svar!(vars[1].clone());
    let m = svar!(vars[0].clone());

    // for reuse
    let mut todo = Vec::new();

    let mut ors: Vec<_> = ctx
        .pbl
        .steps
        .values()
        .map(|s| {
            let s_vars = s.occuring_variables().clone();

            let step_f = sfun!(
                s.function(),
                s.free_variables()
                    .iter()
                    .cloned()
                    .map(|v| svar!(v))
                    .collect()
            );
            let order = sfun!(lt; step_f, tp.clone());
            // let content = preprocess(subt, &m, s, &ctx.pbl);

            let content = {
                let mut ors = Vec::new();
                todo.clear();

                todo.push(s.message());
                todo.push(s.condition());

                while let Some(f) = todo.pop() {
                    match f {
                        RichFormula::Fun(f, _) if f.is_from_quantifer() => {
                            let q = ctx
                                .pbl
                                .quantifiers
                                .iter()
                                .find(|q| &q.function == f)
                                .unwrap();
                            todo.extend(q.iter_content())
                        }
                        _ => {}
                    }
                    let (litteral, next) = preprocess(subt, &m, s, &ctx.pbl, f);
                    todo.extend(next.into_iter());
                    if let Some(lit) = litteral {
                        if !ors.contains(&lit) {
                            ors.push(lit)
                        }
                    }
                }
                ors
            };
            SmtFormula::Exists(
                s_vars,
                Box::new(SmtFormula::And(vec![order, SmtFormula::Or(content)])),
            )
        })
        .collect();

    let input_f = sfun!(input; tp.clone());
    if subt.sort() == msg {
        ors.push(seq!(m.clone(), input_f.clone()))
    }
    assertions.push(Smt::Assert(SmtFormula::Forall(
        vars,
        Box::new(simplies!(ctx.env();
            subt.main(m.clone(), input_f, &msg),
            SmtFormula::Or(ors)
        )),
    )));
}

pub fn default_f<'a, 'b>() -> impl Fn(
    &Subterm,
    &SmtFormula,
    &Step,
    &'a Problem,
    &'b RichFormula,
) -> (Option<SmtFormula>, Vec<&'b RichFormula>) {
    move |subt, m, _, _, f| {
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

fn generate_special_subterm(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm {
    let bool = BOOL(ctx.env());

    let input = INPUT(ctx.env()).clone();
    let f_main = Function::new_with_flag(name, vec![], bool.clone(), FFlags::SUBTERM_FUN);
    let f_secondary = Function::new_with_flag(
        &format!("{}_bis", name),
        vec![],
        bool.clone(),
        FFlags::SUBTERM_FUN,
    );

    let step_sort = &STEP(ctx.env()).clone();

    assert!(ctx.env_mut().add_f(f_main.clone()));
    assert!(ctx.env_mut().add_f(f_secondary.clone()));

    let subt = Subterm::VampireSpecial {
        sort: sort.clone(),
        vampire_subterm_fun: SUBTERM(ctx.env()).clone(),
        main: f_main.clone(),
        secondary: f_secondary.clone(),
    };

    let funs_main = ctx
        .env()
        .get_functions_iter()
        .filter(|&f| {
            f.is_term_algebra()
                && !f.is_special_subterm()
                && !functions.contains(&f)
                && !f.is_from_step()
        })
        .cloned()
        .collect_vec();
    let funs_secondary = funs_main
        .iter()
        .cloned()
        .chain(std::iter::once(input.clone()))
        .collect_vec();

    declarations.push(Smt::DeclareSubtermRelation(f_main, funs_main.clone()));
    declarations.push(Smt::DeclareSubtermRelation(
        f_secondary,
        funs_secondary.clone(),
    ));

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
            sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.main(m, m2, s))}),
        ));
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.secondary(m, m2, s))}),
        ));
    }
    if sort.is_term_algebra() {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort; {subt.main(m.clone(), m, sort)}),
        ));
        assertions.push(Smt::Assert(
            sforall!(m!1:sort; {subt.secondary(m.clone(), m, sort)}),
        ));
    } else {
        for s in subt.iter() {
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

fn generate_base_subterm(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm {
    let bool = BOOL(ctx.env()).clone();
    let input = INPUT(ctx.env()).clone();
    let step_sort = &STEP(ctx.env()).clone();

    let sorts = ctx
        .env()
        .get_sort_iter()
        .cloned()
        // .filter(Sort::is_term_algebra)
        .collect_vec();
    let (main, secondary): (Vec<_>, Vec<_>) = sorts
        .iter()
        .map(|s| {
            let main = Function::new_with_flag(
                &format!("s$subterm_{}_{}", name, s.name()),
                vec![sort.clone(), s.clone()],
                bool.clone(),
                FFlags::empty(),
            );
            let secondary = Function::new_with_flag(
                &format!("s$subterm_{}_{}_bis", name, s.name()),
                vec![sort.clone(), s.clone()],
                bool.clone(),
                FFlags::empty(),
            );

            assert!(ctx.env_mut().add_f(main.clone()));
            assert!(ctx.env_mut().add_f(secondary.clone()));

            (main, secondary)
        })
        .unzip();

    let subterm = Subterm::Base {
        sort: sort.clone(),
        sorts_order: sorts,
        main: main,
        secondary: secondary,
        name: name.to_owned(),
    };

    // declare all functions
    if let Subterm::Base {
        main, secondary, ..
    } = &subterm
    {
        declarations.extend(
            main.iter()
                .chain(secondary.iter())
                .cloned()
                .map(|f| Smt::DeclareFun(f)),
        )
    } else {
        unreachable!()
    }


    // functions on which the subterm commutes "blindly"
    let funs_main = ctx
        .env()
        .get_functions_iter()
        .filter(|&f| {
            f.is_term_algebra()
                && !f.is_special_subterm()
                && !functions.contains(&f)
                && !f.is_from_step()
        })
        .cloned()
        .collect_vec();

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

            subterm
                .iter()
                // zip it with copies of 'or_formulas'
                .zip([or_formulas.clone(), or_formulas].into_iter())
                .map(|(s, mut or_formulas)| {
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
        });
        assertions.extend(iter);

        {
            let msg = MSG(ctx.env());
            let step = STEP(ctx.env());

            let f = if sort == msg {
                sforall!(x!1:sort, s!2:step; {
                    simplies!(ctx.env();
                        subterm.secondary(x.clone(), sfun!(input; s.clone()), msg),
                        seq!(x.clone(), sfun!(input; s))
                )
                })
            } else {
                sforall!(x!1:sort, s!2:step; {
                    snot!(ctx.env();
                        subterm.secondary(x.clone(), sfun!(input; s.clone()), msg)
                )
                })
            };
            assertions.push(Smt::Assert(f));
        }
    }

    if let Subterm::Base { sorts_order, .. } = &subterm {
        assertions.extend(
            sorts_order
                .iter()
                .filter(|&s| !s.is_term_algebra() && (s != sort) && (s != step_sort))
                .flat_map(|s| {
                    subterm
                        .iter()
                        .map(|subt| sforall!(x!1:sort, n!2:s; {snot!(ctx.env(); subt.f(x, n, s))}))
                })
                .map(|f| Smt::Assert(f)),
        )
    } else {
        unreachable!()
    }

    if sort.is_term_algebra() {
        for s in subterm.iter() {
            assertions.push(Smt::Assert(sforall!(m!1:sort; {s.f(m.clone(), m, sort)})))
        }
    } else {
        for s in subterm.iter() {
            assertions.push(Smt::Assert(sforall!(m!1:sort, m2!2:sort; {
                simplies!(ctx.env();
                    s.f(m.clone(), m2.clone(), sort),
                    seq!(m, m2)
                )
            })))
        }
    }

    subterm
}

fn spliting(assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>, ctx: &mut Ctx, subt: &Subterm) {
    let input = INPUT(ctx.env());
    let lt = ctx.env().get_f(LT_NAME).unwrap();
    let msg = MSG(ctx.env());
    let cond = CONDITION(ctx.env());

    // biggest than any step variable
    let max_var = ctx
        .pbl
        .steps
        .values()
        .map(|s| s.vairable_range().end)
        .max()
        .unwrap_or(0);

    // make ununsed variables
    let sorts = vec![subt.sort().clone(), STEP(ctx.env()).clone()];
    let vars = sorts_to_variables(max_var, sorts.iter());

    declarations.reserve(ctx.pbl.steps.len());
    assertions.reserve(ctx.pbl.steps.len() + 1);
    let mut premises = Vec::with_capacity(ctx.pbl.steps.len());

    let m = SmtFormula::from(&vars[0]);
    let tp = SmtFormula::from(&vars[1]);

    for s in ctx.pbl.steps.values() {
        let sp = Function::new_with_flag(
            &format!("sp${}${}", subt.as_main().name(), s.name()),
            sorts.clone(),
            BOOL(ctx.env()).clone(),
            FFlags::SPLITING,
        );
        let sp_const = sfun!(sp, vars.iter().map_into().collect());

        declarations.push(Smt::DeclareFun(sp.clone()));
        premises.push(sp_const.clone());

        // variables 0 was `in`
        let step_vars = sorts_to_variables(1, s.parameters());

        assertions.push(Smt::Assert(sforall!(
            vars.clone(),
            simplies!(ctx.env();
                sp_const.clone(),
                sexists!(
                    step_vars.clone(),
                    sand!(
                        sfun!(lt; sfun!(
                            s.function(),
                            step_vars.iter().map_into().collect()),
                        tp.clone()),
                        sor!(
                            subt.secondary(m.clone(), s.message().into(), msg),
                            subt.secondary(m.clone(), s.condition().into(), cond)
                        )
                    )
                )
            )
        )))
    }

    if subt.sort() == msg {
        premises.push(seq!(m.clone(), sfun!(input; tp.clone())));
    }

    assertions.push(Smt::Assert(sforall!(
        vars.clone(),
        simplies!(ctx.env();
            subt.main(m.clone(), sfun!(input; tp.clone()), msg),
            SmtFormula::Or(premises)
        )
    )))
}
