use std::collections::HashMap;

use crate::{
    formula::{
        builtins::{
            functions::{
                self, AND, AND_NAME, B_EQUALITY, B_IF_THEN_ELSE, EQUALITY_NAME, EVAL_COND,
                EVAL_MSG, FALSE, FALSE_NAME, IF_THEN_ELSE_NAME, NOT, NOT_NAME, OR, OR_NAME, TRUE,
                TRUE_NAME,
            },
            types::{BITSTRING, BOOL, CONDITION, CONDITION_NAME, MSG, MSG_NAME},
        },
        formula::{RichFormula, Variable},
        function::{Flags, Function},
        macros::fun,
        quantifier::{self, Quantifier},
        sort::Sort,
    },
    utils::{clone_iter, replace_if_eq},
};

use super::{crypto_assumptions::CryptoAssumption, protocol::Step};

#[derive(Debug)]
pub struct Problem {
    steps: HashMap<String, Step>,
    functions: HashMap<String, Function>,
    sorts: Vec<Sort>,
    assertions: Vec<RichFormula>,
    query: RichFormula,
    order: Vec<RichFormula>,
    lemmas: Vec<RichFormula>,
    crypto_assumptions: Vec<CryptoAssumption>,
    quantifiers: Vec<QuantifierP>
}

pub struct ProblemBuilder {
    steps: Vec<Step>,
    functions: Vec<Function>,
    sorts: Vec<Sort>,
    assertions: Vec<RichFormula>,
    query: RichFormula,
    order: Vec<RichFormula>,
    temporary: Vec<RichFormula>,
    crypto_assumptions: Vec<CryptoAssumption>,
}

#[derive(Debug)]
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

#[derive(Debug)]
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

const CAND_NAME: &'static str = "c$and";
const COR_NAME: &'static str = "c$or";
const CNOT_NAME: &'static str = "c$not";
const CEQ_NAME: &'static str = "c$eq";
const CTRUE_NAME: &'static str = "c$true";
const CFALSE_NAME: &'static str = "c$false";

impl Problem {
    pub fn new(pbl: ProblemBuilder) -> Self {
        let ProblemBuilder {
            steps,
            functions,
            sorts,
            assertions,
            query,
            order,
            temporary,
            crypto_assumptions,
        } = pbl;

        // ensure all term algebra functions use the right sorts
        let term_algebra_functions: Vec<Function> = functions
            .iter()
            .filter(|f| f.is_term_algebra())
            .map(|f| {
                let name = f.name();
                let in_s = f
                    .get_input_sorts()
                    .iter()
                    .map(|s| replace_if_eq(s.clone(), BOOL.clone(), CONDITION.clone()))
                    .collect();
                let out_s =
                    replace_if_eq(f.get_output_sort().clone(), BOOL.clone(), CONDITION.clone());
                let flags = f.get_flags();
                Function::new_with_flag(name, in_s, out_s, flags)
            })
            .collect();

        // get the evaluate version of thos function (skipping the special cases)
        let evaluated_functions: Vec<Function> = term_algebra_functions
            .iter()
            .filter_map(get_evaluate_fun)
            .collect();

        // some special functions
        let flag = Flags::SPECIAL_EVALUATE | Flags::TERM_ALGEBRA;
        let function_db = FunctionDB {
            cand: Function::new_with_flag(
                CAND_NAME,
                vec![CONDITION.clone(), CONDITION.clone()],
                CONDITION.clone(),
                flag,
            ),
            cor: Function::new_with_flag(
                COR_NAME,
                vec![CONDITION.clone(), CONDITION.clone()],
                CONDITION.clone(),
                flag,
            ),
            cnot: Function::new_with_flag(
                CNOT_NAME,
                vec![CONDITION.clone()],
                CONDITION.clone(),
                flag,
            ),
            ceq: Function::new_with_flag(
                CEQ_NAME,
                vec![MSG.clone(), MSG.clone()],
                CONDITION.clone(),
                flag,
            ),
            ctrue: Function::new_with_flag(CTRUE_NAME, vec![], CONDITION.clone(), flag),
            cfalse: Function::new_with_flag(CFALSE_NAME, vec![], CONDITION.clone(), flag),
        };

        // add everything to the the hashtable
        let mut functions = term_algebra_functions
            .into_iter()
            .chain(evaluated_functions.into_iter())
            .chain(function_db.as_vec().iter().map(|f| Function::clone(f)))
            .map(|f| (f.name().to_owned(), f))
            .collect();

        // to keep track of the ta quantifiers
        let mut quantifiers = Vec::new();

        // the steps and collect the ta quantifiers
        let steps: Vec<Step> = steps
            .into_iter()
            .map(|s| {
                let msg = process_step_content(
                    &function_db,
                    &mut functions,
                    &mut quantifiers,
                    s.message(),
                );
                let cond = process_step_content(
                    &function_db,
                    &mut functions,
                    &mut quantifiers,
                    s.condition(),
                );
                let name = s.name();

                Step::new(name, s.parameters().clone(), cond, msg)
            })
            .collect();

        // add the quantifier to the set of functions
        functions.extend(
            quantifiers
                .iter()
                .map(|q| (q.function.name().to_owned(), q.function.clone())),
        );

        // no longer mutable
        let functions = functions;
        let quantifiers = quantifiers;

        // NB: no more ta quantifiers from now on

        let user_assertions: Vec<RichFormula> = assertions
            .into_iter()
            .map(|f| process_assertion(&functions, f))
            .collect();
        let query: RichFormula = process_query(&functions, query);
        let lemmas: Vec<RichFormula> = temporary
            .into_iter()
            .map(|f| process_query(&functions, f))
            .collect();
        let order: Vec<RichFormula> = order
            .into_iter()
            .map(|f| process_oder(&functions, f))
            .collect();

        Problem {
            steps: steps
                .into_iter()
                .map(|s| (s.name().to_owned(), s))
                .collect(),
            functions,
            sorts,
            assertions: user_assertions,
            query,
            order,
            lemmas,
            quantifiers,
            crypto_assumptions,
        }
    }
}

// assertions must be turned into evaluate form
fn process_assertion(functions: &HashMap<String, Function>, f: RichFormula) -> RichFormula {
    turn_formula_into_evaluate(functions, f)
}

// assertions must be turned into evaluate form
fn process_query(functions: &HashMap<String, Function>, f: RichFormula) -> RichFormula {
    turn_formula_into_evaluate(functions, f)
}

fn process_oder(functions: &HashMap<String, Function>, f: RichFormula) -> RichFormula {
    f
}

// from ta to evaluate
//
// panic if there is a plain tfst
fn turn_formula_into_evaluate(
    functions: &HashMap<String, Function>,
    f: RichFormula,
) -> RichFormula {
    fn map_var(v: Variable) -> Variable {
        match v.sort.name() {
            MSG_NAME => Variable {
                sort: BITSTRING.clone(),
                ..v
            },
            CONDITION_NAME => Variable {
                sort: BOOL.clone(),
                ..v
            },
            _ => v,
        }
    }

    fn map_quant(q: Quantifier) -> Quantifier {
        match q {
            Quantifier::Exists { variables } => Quantifier::Exists {
                variables: variables.into_iter().map(map_var).collect(),
            },
            Quantifier::Forall { variables } => Quantifier::Forall {
                variables: variables.into_iter().map(map_var).collect(),
            },
            _ => unreachable!(),
        }
    }

    match f {
        RichFormula::Var(v) => RichFormula::Var(map_var(v)),
        RichFormula::Fun(fun, args) => {
            let eargs = args
                .into_iter()
                .map(|f| turn_formula_into_evaluate(functions, f))
                .collect();
            match fun.name() {
                // dumb base term algebra
                _ if fun.is_term_algebra() && !fun.is_special_evaluate() => RichFormula::Fun(
                    functions.get(&get_evaluate_fun_name(&fun)).unwrap().clone(),
                    eargs,
                ),

                // special ones
                CAND_NAME => RichFormula::Fun(AND.clone(), eargs),
                COR_NAME => RichFormula::Fun(OR.clone(), eargs),
                CNOT_NAME => RichFormula::Fun(NOT.clone(), eargs),
                CEQ_NAME => RichFormula::Fun(B_EQUALITY.clone(), eargs),
                CTRUE_NAME => RichFormula::Fun(TRUE.clone(), eargs),
                CFALSE_NAME => RichFormula::Fun(FALSE.clone(), eargs),
                IF_THEN_ELSE_NAME => RichFormula::Fun(B_IF_THEN_ELSE.clone(), eargs),

                // wierder
                _ if fun.get_output_sort() == &MSG.clone() => {
                    fun!(EVAL_MSG; RichFormula::Fun(fun, eargs))
                }
                _ if fun.get_output_sort() == &CONDITION.clone() => {
                    fun!(EVAL_COND; RichFormula::Fun(fun, eargs))
                }

                // non-term algebra, leave as is
                _ => {
                    assert!(!(fun.contain_sort(&MSG) || fun.contain_sort(&CONDITION)));
                    RichFormula::Fun(fun, eargs)
                }
            }
        }
        RichFormula::Quantifier(q, args) => {
            let eargs = args
                .into_iter()
                .map(|f| turn_formula_into_evaluate(functions, f))
                .collect();
                RichFormula::Quantifier(map_quant(q), eargs)
        },
    }
}

/// get the name of the evaluate version of a ta function
///
/// shouldn't be called if `f` isn't in the ta or has a special
/// evaluate, the result would be unsound
fn get_evaluate_fun_name(f: &Function) -> String {
    assert!(!f.is_special_evaluate() && f.is_term_algebra());
    format!("b_{}", f.name())
}

/// get the evaluate version of a term algebra function
/// skip the [`Flags::SPECIAL_EVALUATE`] functions
fn get_evaluate_fun(f: &Function) -> Option<Function> {
    if f.is_term_algebra() && !f.is_special_evaluate() {
        assert!((f.contain_sort(&CONDITION) || f.contain_sort(&MSG)));
        let name = get_evaluate_fun_name(f);
        let n_in_s = {
            f.get_input_sorts()
                .iter()
                .map(|f| {
                    replace_if_eq(
                        replace_if_eq(f.clone(), CONDITION.clone(), BOOL.clone()),
                        MSG.clone(),
                        BITSTRING.clone(),
                    )
                })
                .collect()
        };
        let n_out_s = {
            replace_if_eq(
                replace_if_eq(f.get_output_sort().clone(), CONDITION.clone(), BOOL.clone()),
                MSG.clone(),
                BITSTRING.clone(),
            )
        };

        Some(Function::new_with_flag(
            &name,
            n_in_s,
            n_out_s,
            Flags::EVALUATE_TA,
        ))
    } else {
        None
    }
}

/// turn whatever format `formula` has into a term algebra one
fn process_step_content<'a>(
    function_db: &FunctionDB,
    functions: &mut HashMap<String, Function>,
    quantifiers: &mut Vec<QuantifierP>,
    formula: &RichFormula,
) -> RichFormula {
    let free_vars: Vec<Variable> = {
        formula
            .get_free_vars()
            .iter()
            .map(|v| Variable::clone(v))
            .collect()
    };
    let sort = formula.get_sort().clone();

    match formula {
        RichFormula::Var(_) => formula.clone(),
        RichFormula::Quantifier(Quantifier::Forall { variables }, args) => {
            let content = process_step_content(
                function_db,
                functions,
                quantifiers,
                args.into_iter().next().unwrap(),
            );
            make_quantifier(
                functions,
                quantifiers,
                free_vars,
                sort,
                variables,
                QuantifierPContent::Forall { content },
                "forall",
            )
        }
        RichFormula::Quantifier(Quantifier::Exists { variables }, args) => {
            let content = process_step_content(
                function_db,
                functions,
                quantifiers,
                args.into_iter().next().unwrap(),
            );
            make_quantifier(
                functions,
                quantifiers,
                free_vars,
                sort,
                variables,
                QuantifierPContent::Exists { content },
                "exists",
            )
        }
        RichFormula::Quantifier(Quantifier::FindSuchThat { variables }, args) => {
            let mut arg_iter = args
                .into_iter()
                .map(|f| process_step_content(function_db, functions, quantifiers, f));
            let condition = arg_iter.next().unwrap();
            let left = arg_iter.next().unwrap();
            let right = arg_iter.next().unwrap();
            make_quantifier(
                functions,
                quantifiers,
                free_vars,
                sort,
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
            let nf = match f.name() {
                AND_NAME => function_db.cand.clone(),
                OR_NAME => function_db.cor.clone(),
                NOT_NAME => function_db.cnot.clone(),
                EQUALITY_NAME => function_db.ceq.clone(),
                TRUE_NAME => function_db.ctrue.clone(),
                FALSE_NAME => function_db.cfalse.clone(),
                name => functions.get(name).unwrap().clone(),
            };
            let nargs = args
                .into_iter()
                .map(|f| process_step_content(function_db, functions, quantifiers, f))
                .collect();
            RichFormula::Fun(nf, nargs)
        }
    }
}

struct FunctionDB {
    cand: Function,
    cor: Function,
    cnot: Function,
    ceq: Function,
    ctrue: Function,
    cfalse: Function,
}

impl FunctionDB {
    fn as_vec(&self) -> Vec<&Function> {
        vec![
            &self.cand,
            &self.cor,
            &self.cnot,
            &self.ceq,
            &self.ctrue,
            &self.cfalse,
        ]
    }
}

fn make_quantifier(
    functions: &mut HashMap<String, Function>,
    quantifiers: &mut Vec<QuantifierP>,
    free_vars: Vec<Variable>,
    sort: Sort,
    variables: &Vec<Variable>,
    content: QuantifierPContent,
    name: &str,
) -> RichFormula {
    let function = Function::new_with_flag(
        &format!("m${}_{}", name, quantifiers.len()),
        free_vars.iter().map(|f| f.sort.clone()).collect(),
        sort,
        Flags::TERM_ALGEBRA | Flags::SPECIAL_EVALUATE,
    );
    functions.insert(function.name().to_owned(), function.clone());
    quantifiers.push(QuantifierP {
        bound_variables: variables.clone(),
        free_variables: free_vars.iter().map(|v| Variable::clone(v)).collect(),
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
