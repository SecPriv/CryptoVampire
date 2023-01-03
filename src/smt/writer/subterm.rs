use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{INPUT, LT_NAME, SUBTERM},
            types::{BOOL, CONDITION, MSG, STEP},
        },
        env::Environement,
        formula::sorts_to_variables,
        function::{FFlags, Function},
        sort::Sort,
    },
    smt::{
        macros::{sand, sexists, sforall, sfun, simplies, snot, sor},
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
        let i = sorts.iter().position(|s| s == sort).unwrap();
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
            Subterm::VampireSpecial { main: f, .. } => f.name().to_owned(),
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

pub(crate) fn generate_subterm(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    name: &str,
    sort: &Sort,
    functions: Vec<&Function>,
) -> Subterm {
    debug_assert!( ctx.pbl.env.verify_f());
    debug_assert!(
        functions.iter().all(|f| ctx.pbl.env.contains_f(f)),
        "\n\tfuns: {:?}\n\tf2: {:?}",
        &functions,
        ctx.pbl.env.get_functions_iter().collect_vec()
    );

    let subt = if ctx.pbl.env.use_special_subterm() {
        generate_special_subterm( assertions, declarations, ctx, name, sort, functions)
    } else {
        todo!()
    };

    // spliting(assertions, declarations, ctx, subt.as_main());
    // spliting(assertions, declarations, ctx, subt.as_secondary());

    for s in subt.iter() {
        spliting(assertions, declarations, ctx, s);
    }

    subt
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

    assert!(ctx.env_mut().add_f(f_main.clone()));
    assert!(ctx.env_mut().add_f(f_secondary.clone()));

    let subt = Subterm::VampireSpecial {
        sort: sort.clone(),
        vampire_subterm_fun: SUBTERM(ctx.env()).clone(),
        main: f_main.clone(),
        secondary: f_secondary.clone(),
    };

    let funs_main = ctx.env()
        .get_functions_iter()
        .filter(|&f| f.is_term_algebra() && !f.is_special_subterm() && !functions.contains(&f))
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

    for s in ctx.env()
        .get_sort_iter()
        .filter(|&s| (s != sort) && !s.is_term_algebra())
    {
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.main(m, m2, s))}),
        ));
        assertions.push(Smt::Assert(
            sforall!(m!1:sort, m2!2:s; {snot!(ctx.env(); subt.secondary(m, m2, s))}),
        ));
    }
    assertions.push(Smt::Assert(
        sforall!(m!1:sort; {subt.main(m.clone(), m, sort)}),
    ));
    assertions.push(Smt::Assert(
        sforall!(m!1:sort; {subt.secondary(m.clone(), m, sort)}),
    ));

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

    let sorts = ctx.env()
        .get_sort_iter()
        .cloned()
        .filter(Sort::is_term_algebra)
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


    subterm
}

fn spliting(
    assertions: &mut Vec<Smt>,
    declarations: &mut Vec<Smt>,
    ctx: &mut Ctx,
    subt: OneSubterm,
) {
    let input = INPUT(ctx.env());
    let lt = ctx.env().get_f(LT_NAME).unwrap();
    let msg = MSG(ctx.env());
    let cond = CONDITION(ctx.env());

    // biggest than any step variable
    let max_var = ctx
        .pbl
        .steps
        .values()
        .map(|s| s.parameters().len())
        .max()
        .unwrap_or(0)
        + 1;
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
            &format!("sp${}${}", subt.name(), s.name()),
            sorts.clone(),
            BOOL(ctx.env()).clone(),
            FFlags::SPLITING,
        );
        let sp_const = sfun!(sp, vars.iter().map_into().collect());

        declarations.push(Smt::DeclareFun(sp.clone()));
        premises.push(sp_const.clone());

        // variables 0 was `in`
        let step_vars = sorts_to_variables(1, s.parameters().iter());

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
                            subt.f(m.clone(), s.message().into(), msg),
                            subt.f(m.clone(), s.condition().into(), cond)
                        )
                    )
                )
            )
        )))
    }

    assertions.push(Smt::Assert(sforall!(
        vars.clone(),
        simplies!(ctx.env();
            subt.f(m.clone(), sfun!(input; tp.clone()), msg),
            SmtFormula::Or(premises)
        )
    )))
}
