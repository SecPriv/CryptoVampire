use std::{collections::HashMap, ops::Deref};

use itertools::Itertools;

use crate::{
    formula::{
        builtins::{
            functions::{
                AND, AND_NAME, B_EQUALITY, B_EQUALITY_NAME, B_IF_THEN_ELSE, B_IF_THEN_ELSE_NAME,
                EQUALITY, EQUALITY_NAME, EVAL_COND, EVAL_MSG, FALSE_NAME, IF_THEN_ELSE,
                IF_THEN_ELSE_NAME, NOT, NOT_NAME, OR, OR_NAME, TRUE_NAME,
            },
            steps::{INIT, INIT_NAME},
            types::{BITSTRING, BOOL, CONDITION, MSG},
        },
        env::Environement,
        formula::{RichFormula, Variable},
        formula_user::{FunctionShortcuter, HasShortcut},
        function::{FFlags, Function},
        macros::fun,
        quantifier::Quantifier,
        sort::Sort,
    },
    utils::utils::replace_if_eq,
};

use super::{
    cell::{Assignement, MemoryCell, PreMemoryCell},
    crypto_assumptions::CryptoAssumption,
    step::Step,
};

#[derive(Debug)]
pub struct Problem {
    pub steps: HashMap<String, Step>,
    pub memory_cells: HashMap<String, MemoryCell>,
    pub env: Environement,
    pub assertions: Vec<RichFormula>,
    pub query: RichFormula,
    pub order: Vec<RichFormula>,
    pub lemmas: Vec<RichFormula>,
    pub crypto_assumptions: Vec<CryptoAssumption>,
    pub quantifiers: Vec<QuantifierP>,
}

pub struct ProblemBuilder {
    pub steps: Vec<Step>,
    pub memory_cells: Vec<PreMemoryCell>,
    pub env: Environement,
    pub assertions: Vec<RichFormula>,
    pub query: RichFormula,
    pub order: Vec<RichFormula>,
    pub lemmas: Vec<RichFormula>,
    pub crypto_assumptions: Vec<CryptoAssumption>,
}

#[derive(Debug, Clone)]
pub struct QuantifierP {
    /// variables bounded by this quantifier
    pub bound_variables: Vec<Variable>,
    /// variables that appear within this quantifiers
    /// but are not bound by it (those are passed through)
    pub free_variables: Vec<Variable>,
    /// the function for the naming
    pub function: Function,
    /// the actual content
    pub content: QuantifierPContent,
}

#[derive(Debug, Clone)]
pub enum QuantifierPContent {
    Exists {
        content: RichFormula,
    },
    Forall {
        content: RichFormula,
    },
    FindSuchThat {
        condition: RichFormula,
        left: RichFormula,
        right: RichFormula,
    },
}

impl QuantifierP {
    pub fn iter_content<'a>(&'a self) -> impl Iterator<Item = &'a RichFormula> {
        match &self.content {
            QuantifierPContent::Exists { content } | QuantifierPContent::Forall { content } => {
                vec![content].into_iter()
            }
            QuantifierPContent::FindSuchThat {
                condition,
                left,
                right,
            } => vec![condition, left, right].into_iter(),
        }
    }
}

pub const CAND_NAME: &'static str = "c$and";
pub const COR_NAME: &'static str = "c$or";
pub const CNOT_NAME: &'static str = "c$not";
pub const CEQ_NAME: &'static str = "c$eq";
pub const CTRUE_NAME: &'static str = "c$true";
pub const CFALSE_NAME: &'static str = "c$false";

impl Problem {
    pub fn new(pbl: ProblemBuilder) -> Self {
        let ProblemBuilder {
            steps,
            memory_cells,
            mut env,
            assertions,
            query,
            order,
            lemmas: temporary,
            crypto_assumptions,
        } = pbl;

        let cond = CONDITION(&env).clone();
        let msg = MSG(&env).clone();
        let bool = BOOL(&env).clone();
        let bitstring = BITSTRING(&env).clone();

        // add and build easy to easy to acces functions & steps
        let function_db = {
            let flag = FFlags::SPECIAL_EVALUATE | FFlags::TERM_ALGEBRA;

            let cand = env.create_and_add_function(CAND_NAME, &[&cond, &cond], &cond, flag);
            let cor = env.create_and_add_function(COR_NAME, &[&cond, &cond], &cond, flag);
            let cnot = env.create_and_add_function(CNOT_NAME, &[&cond], &cond, flag);
            let ceq = env.create_and_add_function(CEQ_NAME, &[&msg, &msg], &cond, flag);
            let ctrue = env.create_and_add_function(CTRUE_NAME, &[], &cond, flag);
            let cfalse = env.create_and_add_function(CFALSE_NAME, &[], &cond, flag);
            let item = IF_THEN_ELSE(&env).clone();

            cand.set_evaluate_functions(AND(&env));
            cor.set_evaluate_functions(OR(&env));
            cnot.set_evaluate_functions(NOT(&env));
            ceq.set_evaluate_functions(B_EQUALITY(&env));
            item.set_evaluate_functions(B_IF_THEN_ELSE(&env));

            {
                let eq = EQUALITY(&env);
                eq.set_evaluate_functions(eq)
            }

            QuickAccess {
                cand,
                cor,
                cnot,
                ceq,
                ctrue,
                cfalse,
                // init: INIT(&env),
                cond: cond.clone(),
                msg: msg.clone(),
                bool: bool.clone(),
                bitstring: bitstring.clone(),
                item,
            }
        };

        // ensure all term algebra functions use the right sorts
        // get the evaluate version of those function (skipping the special cases)
        let evaluated_functions = env
            .get_functions_iter_mut()
            .filter_map(|f| {
                if f.is_term_algebra() {
                    // dbg!((f.name(), bool.name(), cond.name()));
                    f.set_sort_fun(|s| {
                        // dbg!(s.name());
                        replace_if_eq(&s, &bool, &cond).clone()
                    });

                    generate_evaluate_fun(&function_db, f).map(|nf| (f, nf))
                } else {
                    None
                }
            })
            .map(|(nf, f)| {
                nf.set_evaluate_functions(&f);
                f
            })
            .collect_vec();
        env.extend_functions(evaluated_functions.into_iter());

        // to keep track of the ta quantifiers
        let mut quantifiers = Vec::new();
        let init = INIT(&env).clone();

        // the steps and collect the ta quantifiers
        let steps: Vec<Step> = steps
            .into_iter()
            .chain(std::iter::once(init))
            .map(|s| {
                // let msg = process_step_content(
                //     &function_db,
                //     &mut env,
                //     &mut quantifiers,
                //     &msg,
                //     s.message(),
                // );
                // let cond = process_step_content(
                //     &function_db,
                //     &mut env,
                //     &mut quantifiers,
                //     &cond,
                //     s.condition(),
                // );
                // let name = s.name();

                // Step::new(
                //     name,
                //     s.parameters().clone(),
                //     cond,
                //     msg,
                //     s.function().clone(),
                // )
                s.map(|i, f| {
                    let sort = match i {
                        super::step::MessageOrCondition::Message => &msg,
                        super::step::MessageOrCondition::Condition => &cond,
                    };
                    process_step_content(&function_db, &mut env, &mut quantifiers, sort, f)
                })
            })
            .collect();

        // make sure the steps are in the function set
        for step in &steps {
            env.get_functions_mut()
                .entry(step.name().to_owned())
                .or_insert(step.into()); // skip if already there
        }

        // add the quantifier to the set of functions
        env.extend_functions(quantifiers.iter().map(|q| &q.function).cloned());

        // no longer mutable
        // let env = env;
        let quantifiers = quantifiers;

        // NB: no more ta quantifiers from now on

        let user_assertions: Vec<RichFormula> = assertions
            .into_iter()
            // .map(|f| process_assertion(&function_db, &env, f))
            .map(|f| process_user_formula(&function_db, &env, f))
            .collect();
        let query: RichFormula = process_user_formula(&function_db, &env, query);
        let lemmas: Vec<RichFormula> = temporary
            .into_iter()
            .map(|f| process_user_formula(&function_db, &env, f))
            .collect();
        let order: Vec<RichFormula> = order.into_iter().map(|f| process_oder(&env, f)).collect();

        Problem {
            steps: steps
                .into_iter()
                .map(|s| (s.name().to_owned(), s))
                .collect(),
            memory_cells: memory_cells
                .into_iter()
                .map(|s| (s.name().to_owned(), s.into()))
                .collect(),
            env,
            assertions: user_assertions,
            query,
            order,
            lemmas,
            quantifiers,
            crypto_assumptions,
        }
    }

    pub fn get_init_step(&self) -> &Step {
        self.steps.get(INIT_NAME).unwrap()
    }

    pub fn get_init_step_function(&self) -> &Function {
        self.env.get_f(INIT_NAME).unwrap()
    }

    pub fn iter_content<'a>(&'a self) -> impl Iterator<Item = (&'a Step, &'a RichFormula)> {
        self.steps
            .values()
            .flat_map(|s| [(s, s.message()), (s, s.condition())].into_iter())
    }

    pub fn max_var(&self) -> usize {
        let mut pile = Vec::new();

        let mut max = 0;
        for c in self.memory_cells.values() {
            for Assignement { content, .. } in c.assignements() {
                for Variable { id, .. } in content.used_variables_iter_with_pile(self, &mut pile) {
                    if *id > max {
                        max = *id;
                    }
                }
            }
        }
        for s in self.steps.values() {
            for Variable { id, .. } in s.occuring_variables() {
                if *id > max {
                    max = *id
                }
            }
        }

        max
    }
}

// assertions must be turned into evaluate form
fn process_user_formula(
    function_db: &QuickAccess,
    env: &Environement,
    formula: RichFormula,
) -> RichFormula {
    process_user_formula_content(function_db, env, formula)
}

fn process_oder(_env: &Environement, f: RichFormula) -> RichFormula {
    f
}

mod to_evaluate {
    use crate::formula::{
        builtins::types::{CONDITION_NAME, MSG_NAME},
        formula::Variable,
        quantifier::Quantifier,
    };

    use super::QuickAccess;

    pub(crate) fn map_var(function_db: &QuickAccess, v: Variable) -> Variable {
        match v.sort.name() {
            MSG_NAME => Variable {
                sort: function_db.bitstring.clone(),
                ..v
            },
            CONDITION_NAME => Variable {
                sort: function_db.bool.clone(),
                ..v
            },
            _ => v,
        }
    }

    pub(crate) fn map_quant(fdb: &QuickAccess, q: Quantifier) -> Quantifier {
        match q {
            Quantifier::Exists { variables } => Quantifier::Exists {
                variables: variables.into_iter().map(|v| map_var(fdb, v)).collect(),
            },
            Quantifier::Forall { variables } => Quantifier::Forall {
                variables: variables.into_iter().map(|v| map_var(fdb, v)).collect(),
            },
            _ => unreachable!(),
        }
    }
}

// from ta to evaluate
//
// panic if there is a plain tfst
#[allow(dead_code)]
fn turn_formula_into_evaluate(
    function_db: &QuickAccess,
    env: &Environement,
    f: RichFormula,
) -> RichFormula {
    match f {
        RichFormula::Var(v) => RichFormula::Var(to_evaluate::map_var(function_db, v)),
        RichFormula::Fun(fun, args) => {
            match fun.name() {
                // dumb base term algebra
                _ if fun.is_term_algebra() && !fun.is_special_evaluate() => {
                    let eargs = args
                        .into_iter()
                        .map(|f| turn_formula_into_evaluate(function_db, env, f))
                        .collect();

                    RichFormula::Fun(
                        // functions.get(&get_evaluate_fun_name(&fun).unwrap()).unwrap().clone(),
                        fun.get_evaluate_function()
                            .unwrap_or_else(|| panic!("{:?}", &fun)),
                        eargs,
                    )
                }

                // special ones
                // CAND_NAME => RichFormula::Fun(AND(env).clone(), eargs),
                // COR_NAME => RichFormula::Fun(OR(env).clone(), eargs),
                // CNOT_NAME => RichFormula::Fun(NOT(env).clone(), eargs),
                // CEQ_NAME => RichFormula::Fun(B_EQUALITY(env).clone(), eargs),
                // CTRUE_NAME => RichFormula::Fun(TRUE(env).clone(), eargs),
                // CFALSE_NAME => RichFormula::Fun(FALSE(env).clone(), eargs),
                // IF_THEN_ELSE_NAME => RichFormula::Fun(B_IF_THEN_ELSE(env).clone(), eargs),
                // EQUALITY_NAME => RichFormula::Fun(B_EQUALITY(env).clone(), eargs),
                CAND_NAME | COR_NAME | CNOT_NAME | CEQ_NAME | CTRUE_NAME | CFALSE_NAME
                | IF_THEN_ELSE_NAME | EQUALITY_NAME => {
                    let eargs = args
                        .into_iter()
                        .map(|f| turn_formula_into_evaluate(function_db, env, f))
                        .collect();

                    RichFormula::Fun(
                        fun.get_evaluate_function()
                            .unwrap_or_else(|| panic!("{:?}", &fun)),
                        eargs,
                    )
                }

                // wierder
                // _ if fun.get_output_sort() == MSG(env) => {
                //     fun!(EVAL_MSG(env); RichFormula::Fun(fun, eargs))
                // }
                // _ if fun.get_output_sort() == CONDITION(env) => {
                //     fun!(EVAL_COND(env); RichFormula::Fun(fun, eargs))
                // }
                _ if fun.get_output_sort().is_evaluatable() => {
                    call_evaluate(env, RichFormula::Fun(fun, args))
                }

                // non-term algebra, leave as is
                _ => {
                    debug_assert!(
                        !(fun.contain_sort(MSG(env)) || fun.contain_sort(CONDITION(env))),
                        "{:?}",
                        fun
                    );
                    let eargs = args
                        .into_iter()
                        .map(|f| turn_formula_into_evaluate(function_db, env, f))
                        .collect();
                    RichFormula::Fun(fun, eargs)
                }
            }
        }
        RichFormula::Quantifier(q, args) => {
            let eargs = args
                .into_iter()
                .map(|f| turn_formula_into_evaluate(function_db, env, f))
                .collect();
            RichFormula::Quantifier(to_evaluate::map_quant(function_db, q), eargs)
        }
    }
}

pub fn call_evaluate(env: &Environement, f: RichFormula) -> RichFormula {
    debug_assert!(
        f.get_sort(env).is_evaluatable(),
        "sort: {}",
        f.get_sort(env)
    );
    match &f.get_sort(env) {
        s if s == MSG(env) => fun!(EVAL_MSG(env); f),
        s if s == CONDITION(env) => fun!(EVAL_COND(env); f),
        s => unreachable!("{} is not evaluatable or not implemented", s.name()),
    }
}

/// get the name of the evaluate version of a ta function
///
/// shouldn't be called if `f` isn't in the ta or has a special
/// evaluate, the result would be unsound
pub fn get_evaluate_fun_name(f: &Function) -> Option<String> {
    if !f.is_special_evaluate() && f.is_term_algebra() {
        Some(format!("b_{}", f.name()))
    } else {
        None
    }
}

/// get the evaluate version of a term algebra function
/// skip the [`Flags::SPECIAL_EVALUATE`] functions
fn generate_evaluate_fun(db: &QuickAccess, f: &Function) -> Option<Function> {
    if f.is_term_algebra() && !f.is_special_evaluate() && !f.is_from_step() {
        debug_assert!(
            (f.contain_sort(&db.cond) || f.contain_sort(&db.msg)),
            "{:?}",
            f
        );
        let name = get_evaluate_fun_name(f).unwrap();
        let n_in_s = {
            f.get_input_sorts()
                .iter()
                .map(|f| {
                    replace_if_eq(replace_if_eq(f, &db.cond, &db.bool), &db.msg, &db.bitstring)
                        .clone()
                })
                .collect()
        };
        let n_out_s = {
            replace_if_eq(
                replace_if_eq(&f.get_output_sort(), &db.cond, &db.bool),
                &db.msg,
                &db.bitstring,
            )
            .clone()
        };

        let new_f = Function::new_with_flag(&name, n_in_s, n_out_s, FFlags::EVALUATE_TA);
        f.set_evaluate_functions(&new_f);
        Some(new_f)
    } else {
        None
    }
}

/// turn whatever format `formula` has into a term algebra one
fn process_step_content<S>(
    function_db: &QuickAccess,
    env: &mut Environement,
    quantifiers: &mut Vec<QuantifierP>,
    _expected_sort: S,
    formula: &RichFormula,
) -> RichFormula
where
    S: Deref<Target = Sort>,
{
    let _function = &mut env.get_functions_mut();

    let free_vars: Vec<Variable> = {
        formula
            .get_free_vars()
            .iter()
            .map(|v| Variable::clone(v))
            .collect()
    };
    // let sort = formula.get_sort(env).clone();

    match formula {
        RichFormula::Var(_) => formula.clone(),
        RichFormula::Quantifier(Quantifier::Forall { variables }, args) => {
            let content = process_step_content(
                function_db,
                env,
                quantifiers,
                &function_db.cond,
                args.into_iter().next().unwrap(),
            );
            make_quantifier(
                env,
                quantifiers,
                free_vars,
                CONDITION(env).clone(),
                variables,
                QuantifierPContent::Forall { content },
                "forall",
            )
        }
        RichFormula::Quantifier(Quantifier::Exists { variables }, args) => {
            let content = process_step_content(
                function_db,
                env,
                quantifiers,
                &function_db.cond,
                args.into_iter().next().unwrap(),
            );
            make_quantifier(
                env,
                quantifiers,
                free_vars,
                CONDITION(env).clone(),
                variables,
                QuantifierPContent::Exists { content },
                "exists",
            )
        }
        RichFormula::Quantifier(Quantifier::FindSuchThat { variables }, args) => {
            let mut arg_iter = args
                .into_iter()
                .zip([&function_db.cond, &function_db.msg, &function_db.msg].into_iter())
                .map(|(f, s)| process_step_content(function_db, env, quantifiers, s, f));
            let condition = arg_iter.next().unwrap();
            let left = arg_iter.next().unwrap();
            let right = arg_iter.next().unwrap();
            make_quantifier(
                env,
                quantifiers,
                free_vars,
                MSG(env).clone(),
                variables,
                QuantifierPContent::FindSuchThat {
                    condition,
                    left,
                    right,
                },
                "tfst",
            )
        }
        RichFormula::Fun(f, args) => {
            let nf = get_ta_fun(function_db, f).clone();
            let nargs = args
                .into_iter()
                .zip(f.input_sorts_iter())
                .map(|(f, s)| process_step_content(function_db, env, quantifiers, s, f))
                .collect();
            RichFormula::Fun(nf, nargs)
        }
    }
}

/// turn whatever format `formula` has into a term algebra one
fn process_user_formula_content(
    function_db: &QuickAccess,
    env: &Environement,
    formula: RichFormula,
) -> RichFormula {
    match formula {
        RichFormula::Var(v) => {
            let condition = v.sort.is_evaluatable();
            let f = RichFormula::Var(v);
            if condition {
                call_evaluate(env, f)
            } else {
                f
            }
        }
        RichFormula::Quantifier(Quantifier::FindSuchThat { variables: _ }, _) => {
            panic!("no fst!")
        }
        RichFormula::Quantifier(q, args) => {
            let args = args
                .into_iter()
                .map(|f| process_user_formula_content(function_db, env, f))
                .collect();
            RichFormula::Quantifier(q.clone(), args)
        }
        RichFormula::Fun(f, args) => {
            // if f.is_built_in() {
            //     let args = args
            //         .into_iter()
            //         .map(|f| process_query_content(function_db, env, f))
            //         .collect();
            //     RichFormula::Fun(f, args)
            // } else if f.is_special_evaluate() {
            //     let args = args
            //         .into_iter()
            //         .map(|f| process_query_content(function_db, env, f))
            //         .collect();
            //     RichFormula::Fun(f.get_evaluate_function().unwrap(), args)
            // } else if f.get_output_sort().is_evaluatable() {
            //     call_evaluate(env, RichFormula::Fun(f, args))
            // } else {
            //     unreachable!("{:?}", f)
            // }
            // dbg!(f.name(), f.is_term_algebra());

            if f.is_term_algebra() && f.get_output_sort().is_evaluatable() {
                call_evaluate(env, RichFormula::Fun(f, args))
            } else {
                let args = args
                    .into_iter()
                    .map(|f| process_user_formula_content(function_db, env, f))
                    .collect();
                RichFormula::Fun(f, args)
            }
        }
    }
}

#[allow(unreachable_patterns)]
fn get_ta_fun<'a>(function_db: &'a QuickAccess, f: &'a Function) -> &'a Function {
    match f.name() {
        // _ if f.is_term_algebra() => f,
        AND_NAME => &function_db.cand,
        OR_NAME => &function_db.cor,
        NOT_NAME => &function_db.cnot,
        EQUALITY_NAME => &function_db.ceq,
        TRUE_NAME => &function_db.ctrue,
        B_EQUALITY_NAME => &function_db.ceq,
        FALSE_NAME => &function_db.cfalse,
        B_IF_THEN_ELSE_NAME => &function_db.item,
        _ => f,
        // _ => unreachable!("special evaluate should be treated specially ({:?})", f),
    }
}

pub(crate) struct QuickAccess {
    cand: Function,
    cor: Function,
    cnot: Function,
    ceq: Function,
    ctrue: Function,
    cfalse: Function,
    item: Function,
    // init: Step,
    bool: Sort,
    msg: Sort,
    cond: Sort,
    bitstring: Sort,
}

// impl QuickAccess {
//     fn as_vec(&self) -> Vec<&Function> {
//         vec![
//             &self.cand,
//             &self.cor,
//             &self.cnot,
//             &self.ceq,
//             &self.ctrue,
//             &self.cfalse,
//         ]
//     }
// }

fn make_quantifier(
    env: &mut Environement,
    quantifiers: &mut Vec<QuantifierP>,
    free_vars: Vec<Variable>,
    sort: Sort,
    variables: &Vec<Variable>,
    content: QuantifierPContent,
    name: &str,
) -> RichFormula {
    debug_assert!(
        free_vars
            .iter()
            .cartesian_product(variables.iter())
            .all(|(a, b)| a != b),
        "\n\tfv: {:?}\n\tbv: {:?}\n\tq: {:?}",
        &free_vars,
        &variables,
        &content
    );

    let function = Function::new_with_flag(
        &format!("m${}_{}", name, quantifiers.len()),
        free_vars.iter().map(|f| f.sort.clone()).collect(),
        sort,
        FFlags::TERM_ALGEBRA
            | FFlags::SPECIAL_EVALUATE
            | FFlags::SPECIAL_SUBTERM
            | FFlags::FROM_QUANTIFIER,
    );
    env.add_f(function.clone());
    quantifiers.push(QuantifierP {
        bound_variables: variables.clone(),
        free_variables: free_vars.iter().cloned().collect(),
        function: function.clone(),
        content,
    });
    RichFormula::Fun(
        function,
        free_vars
            .iter()
            .map(|v| RichFormula::Var(Variable::clone(v)))
            .collect(),
    )
}

impl HasShortcut for Problem {
    fn get_function_shortcut(&self) -> &FunctionShortcuter {
        self.env.get_function_shortcut()
    }
}
