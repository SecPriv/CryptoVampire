use std::{fmt::Display, ops::Deref};
mod cached_builtins;

use itertools::Itertools;
use log::{log_enabled, trace};
use pest::Span;

use crate::{parser::{
    ast::{self, extra::SnN, Term, VariableBinding},
    err, merr, IntoRuleResult, E,
}, smt::smt::SmtFormula};
use cryptovampire_lib::{
    environement::traits::{KnowsRealm, Realm},
    formula::{
        self,
        formula::{ARichFormula, RichFormula},
        function::{
            self,
            builtin::{IF_THEN_ELSE, IF_THEN_ELSE_TA},
            inner::term_algebra::TermAlgebra,
            signature::Signature,
            Function,
        },
        sort::{
            builtins::{BOOL, CONDITION, MESSAGE, NAME, STEP},
            sort_proxy::SortProxy,
        },
        variable::Variable,
    },
};
use utils::{f, implvec, match_as_trait, maybe_owned::MOw, traits::NicerError, try_trace};

use self::cached_builtins::*;

use super::{
    parsing_environement::{get_function, get_sort, FunctionCache},
    Environement,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct VarProxy<'bump> {
    id: usize,
    sort: SortProxy<'bump>,
}

impl<'bump> VarProxy<'bump> {
    pub fn try_into_variable(&self) -> Option<Variable<'bump>> {
        let VarProxy { id, sort } = self;
        sort.as_option().map(|sort| Variable { id: *id, sort })
    }
}

impl<'bump> Display for VarProxy<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let VarProxy { id, sort } = self;
        write!(f, "(X{id}: ")?;
        match sort.as_option() {
            Some(s) => write!(f, "{s})"),
            None => write!(f, "_)"),
        }
    }
}

impl<'bump> From<Variable<'bump>> for VarProxy<'bump> {
    fn from(value: Variable<'bump>) -> Self {
        Self {
            id: value.id,
            sort: value.sort.into(),
        }
    }
}

pub trait Parsable<'bump, 'str> {
    type R;
    fn parse(
        &self,
        env: &Environement<'bump, 'str>,
        bvars: &mut Vec<(&'str str, VarProxy<'bump>)>,
        state: &impl KnowsRealm, // State<'_, 'str, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E>;
}

impl<'a, 'bump> Parsable<'bump, 'a> for ast::LetIn<'a> {
    type R = ARichFormula<'bump>;

    #[allow(unreachable_code)]
    #[allow(unused_assignments)]
    fn parse(
        &self,
        _env: &Environement<'bump, 'a>,
        _bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        _state: &impl KnowsRealm,
        _expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        return err(merr(
            self.span,
            "let ... in are not supported yet".to_owned(),
        ));
        todo!()

        // // current length of the pile of variable
        // // to be reused for variable indexing, and troncating the pile
        // let vn = bvars.len();

        // // retrieve data
        // let ast::LetIn { var, t1, t2, .. } = self;

        // // defined a new variable of unknown type
        // let v = VarProxy {
        //     id: vn,
        //     sort: Default::default(),
        // };

        // // parse t1 expecting the unknown sort
        // let t1 = t1.parse(env, bvars, &Realm::Symbolic, Some(v.sort.clone()))?;

        // // parse t2
        // let t2 = {
        //     bvars.push((var.name(), v.clone())); // add var to the pile
        //     let t2 = t2.parse(env, bvars, state, expected_sort.clone())?;
        //     bvars.truncate(vn); // remove it from the pile
        //     t2
        // };

        // // replace `v` by its content: `t1`
        // Ok(t2.owned_into_inner().apply_substitution([vn], [&t1]).into())
    }
}
impl<'a, 'bump> Parsable<'bump, 'a> for ast::IfThenElse<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        // generate the expected sorts
        let (es_condition, es_branches): (SortProxy, SortProxy) = match state.get_realm() {
            Realm::Evaluated => (BOOL.as_sort().into(), Default::default()),
            Realm::Symbolic => (CONDITION.as_sort().into(), MESSAGE.as_sort().into()),
        };

        // check sort
        if let Some(es) = &expected_sort {
            es_branches.unify(es, &state).into_rr(self.span)?;
        }

        let ast::IfThenElse {
            condition,
            left,
            right,
            ..
        } = self;

        // parse the argumeents
        let condition = condition.parse(env, bvars, state, Some(es_condition))?;
        let left = left.parse(env, bvars, state, Some(es_branches.clone()))?;
        let right = right.parse(env, bvars, state, Some(es_branches))?;

        Ok(match state.get_realm() {
            Realm::Evaluated => IF_THEN_ELSE.clone(),
            Realm::Symbolic => IF_THEN_ELSE_TA.clone(),
        }
        .f_a([condition, left, right]))
    }
}

impl<'a, 'bump> Parsable<'bump, 'a> for ast::FindSuchThat<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        expected_sort
            .into_iter()
            .try_for_each(|s| s.expects(MESSAGE.as_sort(), &state).into_rr(self.span))?;

        let ast::FindSuchThat {
            vars,
            condition,
            left,
            right,
            ..
        } = self;

        // parse the default case without the extra variables
        let right = right.parse(env, bvars, &Realm::Symbolic, Some(MESSAGE.as_sort().into()))?;

        // for unique ids and truncate
        let bn = bvars.len();

        // build the bound variables
        bvars.reserve(vars.into_iter().len());
        let vars: Result<Vec<_>, _> = vars
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                let id = i + bn;
                let ast::VariableBinding {
                    variable,
                    type_name,
                    ..
                } = v;

                // ensures the name is free
                if env.functions.contains_key(variable.name())
                    || bvars.iter().map(|(n, _)| n).contains(&variable.name())
                {
                    return err(merr(
                        variable.0.span,
                        f!("the name {} is already taken", variable.name()),
                    ));
                }

                let SnN { span, name } = type_name.into();

                let var = Variable {
                    id,
                    sort: get_sort(env, *span, name)?,
                };

                // sneakly expand `bvars`
                // we need this here to keep the name
                let content = (variable.name(), var.into());
                bvars.push(content);

                Ok(var)
            })
            .collect();
        let vars = vars?;

        // parse the rest
        let condition = condition.parse(
            env,
            bvars,
            &Realm::Symbolic,
            Some(CONDITION.as_sort().into()),
        )?;
        let left = left.parse(env, bvars, &Realm::Symbolic, Some(MESSAGE.as_sort().into()))?;

        // remove variables
        bvars.truncate(bn);

        let (f /* the function */, fvars /* the free vars */) =
            Function::new_find_such_that(env.container, vars, condition, left, right);

        let ret = f.f_a(fvars.iter());
        Ok(match state.get_realm() {
            Realm::Symbolic => ret,
            _ => env.evaluator.eval(ret),
        })
    }
}
impl<'a, 'bump> Parsable<'bump, 'a> for ast::Quantifier<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        let ast::Quantifier {
            kind,
            span,
            vars,
            content,
            ..
        } = self;

        let es = match state.get_realm() {
            Realm::Evaluated => BOOL.as_sort().into(),
            Realm::Symbolic => CONDITION.as_sort().into(),
        };
        expected_sort
            .into_iter()
            .try_for_each(|s| s.expects(es, &state).into_rr(*span))?;

        let bn = bvars.len();

        bvars.reserve(vars.into_iter().len());
        let vars: Result<Vec<_>, _> = vars
            .into_iter()
            .enumerate()
            .map(|(i, v)| {
                let id = i + bn;
                let VariableBinding {
                    variable,
                    type_name,
                    ..
                } = v;

                let vname = variable.name();
                // ensures the name is free
                if env.functions.contains_key(vname)
                    || bvars.iter().map(|(n, _)| n).contains(&vname)
                {
                    return err(merr(
                        variable.0.span,
                        f!("the name {} is already taken", vname),
                    ));
                }

                let SnN { span, name } = type_name.into();

                let var = Variable {
                    id,
                    sort: get_sort(env, *span, name)?,
                };

                // sneakly expand `bvars`
                // we need this here to keep the name
                let content = (variable.name(), var.into());
                bvars.push(content);

                Ok(var)
            })
            .collect();
        let vars = vars?.into();

        // parse body
        let content = content.parse(env, bvars, state, Some(es.into()))?;

        // remove bounded variables from pile
        bvars.truncate(bn);

        let q = {
            // let status = match state.get_realm() {
            //     Realm::Evaluated => formula::quantifier::Status::Bool,
            //     Realm::Symbolic => formula::quantifier::Status::Condition,
            // };
            match kind {
                ast::QuantifierKind::Forall => formula::quantifier::Quantifier::Forall {
                    variables: vars,
                    // status,
                },
                ast::QuantifierKind::Exists => formula::quantifier::Quantifier::Exists {
                    variables: vars,
                    // status,
                },
            }
        };

        if cfg!(debug_assertions) {
            try_trace!(
                "parsing quantifier\n\t{}",
                SmtFormula::from_arichformula(&RichFormula::Quantifier(q.clone(), content.clone()))
                    .default_display()
            )
        }

        Ok(match state.get_realm() {
            Realm::Evaluated => RichFormula::Quantifier(q, content).into(),
            Realm::Symbolic => {
                let fq = Function::new_quantifier_from_quantifier(env.container, q, content);

                let args = match fq.as_inner() {
                    function::InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q)) => {
                        q.free_variables.iter()
                    }
                    _ => unreachable!(),
                }
                .map(ARichFormula::from);

                fq.f_a(args)
            }
        })
    }
}
impl<'a, 'bump> Parsable<'bump, 'a> for ast::Application<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        match self {
            ast::Application::ConstVar { span, content } => {
                // check if it is a variable
                bvars
                    .iter()
                    .find(|(s, _)| s == content)
                    .map(|(_, v)| {
                        let VarProxy { id, sort } = v;

                        if sort.is_sosrt(NAME.as_sort()) {
                            err(merr(
                                *span,
                                "assertions with variables of sort Name have a debatable soundness"
                                    .to_string(),
                            ))?
                        }

                        match (
                            sort.as_option().and_then(|s| s.maybe_evaluated_sort()),
                            state.get_realm(),
                        ) {
                            (Some(s), r @ Realm::Evaluated) => {
                                let sort = sort.as_option().unwrap();
                                let formula = env
                                    .evaluator
                                    .get_eval_function(sort)
                                    .expect(&format!(
                                        "{sort} is evaluatable but not in the evaluator..."
                                    ))
                                    .f_a([Variable { id: *id, sort }]);

                                expected_sort
                                    .as_ref()
                                    .map(|es| es.matches(s, &r))
                                    .transpose()
                                    .into_rr(*span)
                                    .map(|_| formula)
                            }
                            (_, r) => expected_sort
                                .as_ref()
                                .map(|es| es.unify_rev(sort, &r).into_rr(*span))
                                .unwrap_or(
                                    sort.as_option()
                                        .ok_or(merr(*span, "can't infer sort".to_string())),
                                )
                                .map(|sort| Variable { id: *id, sort }.into()),
                        }

                        // let sort = expected_sort
                        //     .clone()
                        //     .map(|es| sort.unify(&es, &state).into_rr(*span))
                        //     .unwrap_or_else(|| {
                        //         Into::<Option<Sort>>::into(sort)
                        //             .ok_or_else(|| merr(*span, f!("can't infer sort")))
                        //     })?;

                        // Ok(Variable { id: *id, sort }.into())
                    })
                    // otherwise look for a function
                    .unwrap_or_else(|| {
                        match *content {
                            "true" | "True" => Ok(match state.get_realm() {
                                Realm::Symbolic => TRUE_TA_CACHE(),
                                Realm::Evaluated => TRUE_CACHE(),
                            }),
                            "false" | "False" => Ok(match state.get_realm() {
                                Realm::Symbolic => FALSE_TA_CACHE(),
                                Realm::Evaluated => FALSE_CACHE(),
                            }),
                            content => get_function(env, *span, content).map(MOw::Borrowed),
                        }
                        .and_then(|f| {
                            parse_application(
                                env,
                                span,
                                state,
                                bvars,
                                expected_sort,
                                Deref::deref(&f),
                                [],
                            )
                        })
                    })
            }
            ast::Application::Application {
                span,
                function,
                args,
            } => {
                let content = function.0.content.content;

                match content {
                    "not" => Ok(match state.get_realm() {
                        Realm::Symbolic => NOT_TA_CACHE(),
                        Realm::Evaluated => NOT_CACHE(),
                    }),
                    _ => get_function(env, *span, content).map(MOw::Borrowed),
                }
                .and_then(|f| parse_application(env, span, state, bvars, expected_sort, &f, args))
            }
        }
    }
}

/// parse a function application (when we know it is definitly a function and not a variable)
fn parse_application<'b, 'a, 'bump>(
    env: &'b Environement<'bump, 'a>,
    span: &'b pest::Span<'a>,
    state: &impl KnowsRealm,
    bvars: &'b mut Vec<(&'a str, VarProxy<'bump>)>,
    expected_sort: Option<SortProxy<'bump>>,
    function: &FunctionCache<'a, 'bump>,
    args: implvec!(&'b ast::Term<'a>),
) -> Result<ARichFormula<'bump>, E> {
    if cfg!(debug_assertions) {
        try_trace!("\tparsing head: {}", function.get_function().name())
    }
    // get the evaluated version if needed
    // let fun = match state.get_realm() {
    //     Realm::Evaluated => function
    //         .as_term_algebra()
    //         .maybe_get_evaluated()
    //         .unwrap_or(function),
    //     Realm::Symbolic => function,
    // };

    let signature = function.signature();
    let mut formula_realm = signature.realm();

    // let is_name = signature.out().as_option() == Some(NAME.as_sort());

    // check output sort
    // let _ = expected_sort
    //     .map(|es| {
    //         if is_name {
    //             es.unify_rev(&MESSAGE.as_sort().into(), &state)
    //         } else {
    //             es.unify_rev(&signature.out(), &state)
    //         }
    //     })
    //     .transpose()
    //     .into_rr(*span)?;

    // parse further
    let n_args: Result<Vec<_>, _> = {
        // propagate the right state if it changed
        let state = match &formula_realm {
            Some(r) => *r,
            None => state.get_realm(),
        };
        signature
            .args()
            .into_iter()
            .zip(args.into_iter())
            .map(|(es, t)| t.parse(env, bvars, &state, Some(es)))
            .collect()
    };
    let n_args = n_args?;

    // check arity
    if !signature.args_size().contains(&n_args.len().into()) {
        let range = signature.args_size();
        return err(merr(
            *span,
            f!(
                "wrong number of arguments: got {}, expected [{}, {}]",
                n_args.len(),
                range.start(),
                range.end()
            ),
        ));
    }

    let ifun = function.get_function();
    // if it's a name, cast it
    let formula = if let Some(name) = ifun.as_name() {
        // assert!(is_name);
        formula_realm = Some(Realm::Symbolic); // names are symbolic
        env.name_caster_collection
            .cast(name.target(), ifun.f_a(n_args))
    } else {
        ifun.f_a(n_args)
    };
    // if we are in evaluated land, evaluate
    let formula = match (state.get_realm(), formula_realm) {
        (Realm::Evaluated, Some(Realm::Symbolic)) => env.evaluator.try_eval(formula).unwrap(),
        _ => formula,
    };

    // check output sort
    let out_sort = {
        let mut out_sort = signature.out();
        if out_sort.is_sosrt(NAME.as_sort()) {
            out_sort = MESSAGE.as_sort().into()
        }
        if_chain::if_chain! {
            if state.get_realm() == Realm::Evaluated;
            if formula_realm == Some(Realm::Symbolic);
            if let Some(s) = out_sort.as_option();
            if let Some(es) = s.maybe_evaluated_sort();
            then {
                out_sort = es.into()
            }
        }
        out_sort
    };
    expected_sort
        .map(|es| es.unify_rev(&out_sort, state))
        .transpose()
        .into_rr(*span)?;

    Ok(formula)
}

impl<'a, 'bump> Parsable<'bump, 'a> for ast::AppMacro<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        let Self {
            span: main_span,
            inner,
        } = self;

        match inner {
            ast::InnerAppMacro::Msg(app) | ast::InnerAppMacro::Cond(app) => {
                let step_as_term = app.parse(env, bvars, state, Some(STEP.as_sort().into()))?;

                let args = if let RichFormula::Fun(_, args) = step_as_term.as_ref() {
                    Ok(args)
                } else {
                    err(
                            merr(app.span(), f!("this can only be a plain reference to a step (not just a term of sort {}))", STEP.name()))
                        )
                }?;

                let step_cache = env
                    .functions
                    .get(app.name())
                    .and_then(|fc| fc.as_step())
                    .ok_or_else(|| {
                        merr(
                            app.name_span(),
                            f!("{} is not a known step name", app.name()),
                        )
                    })?;

                let mut nbvars = step_cache.args_vars_with_input().map_into().collect();

                let (to_parse, _) = match inner {
                    ast::InnerAppMacro::Msg(_) => (&step_cache.ast.message, MESSAGE.as_sort()),
                    ast::InnerAppMacro::Cond(_) => (&step_cache.ast.condition, CONDITION.as_sort()),
                    _ => unreachable!(),
                };

                let term = to_parse
                    .parse(env, &mut nbvars, state, expected_sort)
                    .debug_continue()?;

                Ok(term
                    .owned_into_inner()
                    .apply_substitution2(&step_cache.substitution(args.as_ref()))
                    .into())
            }
            ast::InnerAppMacro::Other { name, args } => {
                let mmacro = env
                    .macro_hash
                    .get(name.name())
                    .ok_or_else(|| merr(name.span(), f!("{} is not a known macro", name.name())))?;

                if log_enabled!(log::Level::Trace) {
                    trace!("in macro parsing: {}", name.name());
                    trace!(
                        "\tbvars: [{}]",
                        bvars
                            .iter()
                            .map(|(name, var)| format!("({name} -> {var})"))
                            .join(", ")
                    )
                }

                let args: Vec<_> = if mmacro.args.len() == args.len() {
                    mmacro
                        .args
                        .iter()
                        .zip(args)
                        .map(|(v, arg)| {
                            arg.parse(
                                env,
                                bvars,
                                &v.realm().unwrap_or(state.get_realm()),
                                Some(v.into()),
                            )
                        })
                        .collect()
                } else {
                    err(merr(
                        *main_span,
                        f!(
                            "not enough arguments: expected {}, got {}",
                            mmacro.args.len(),
                            args.len()
                        ),
                    ))
                }?;

                let term = {
                    let mut bvars = mmacro
                        .args
                        .iter()
                        .zip(mmacro.args_name.iter())
                        .enumerate()
                        .map(|(id, (var_sort, var_name))| {
                            (*var_name, Variable::new(id, *var_sort).into())
                        })
                        .collect_vec();
                    mmacro.content.parse(env, &mut bvars, state, expected_sort)
                }?;

                Ok(term
                    .owned_into_inner()
                    .apply_substitution(0..mmacro.args.len(), &args)
                    .into())
            }
        }
    }
}

impl<'a, 'bump> Parsable<'bump, 'a> for ast::Infix<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        match self.operation {
            ast::Operation::HardEq => match self.terms.len() {
                2 => parse_application(
                    env,
                    &self.span,
                    state,
                    bvars,
                    expected_sort,
                    &EQUALITY_TA_CACHE(),
                    &self.terms,
                ),
                _ => Self {
                    operation: ast::Operation::And,
                    span: self.span,
                    terms: as_pair_of_term(
                        self.span,
                        self.operation,
                        self.terms.iter().tuple_windows(),
                    ),
                }
                .parse(env, bvars, state, expected_sort),
            },
            ast::Operation::Eq => match state.get_realm() {
                Realm::Evaluated => parse_application(
                    env,
                    &self.span,
                    state,
                    bvars,
                    expected_sort,
                    &EQUALITY_CACHE(),
                    &self.terms,
                ),
                Realm::Symbolic => Self {
                    operation: ast::Operation::HardEq,
                    ..self.clone()
                }
                .parse(env, bvars, state, expected_sort),
            },
            ast::Operation::Neq => {
                // let not_fun = match state.get_realm() {
                //     Realm::Symbolic => NOT_TA.clone(),
                //     Realm::Evaluated => NOT.clone(),
                // };
                ast::Application::Application {
                    span: self.span,
                    function: ast::Function(ast::Sub {
                        span: self.span,
                        content: ast::Ident {
                            span: self.span,
                            content: "not",
                        },
                    }),
                    args: vec![ast::Term {
                        span: self.span,
                        inner: ast::InnerTerm::Infix(Box::new(Self {
                            operation: ast::Operation::Eq,
                            ..self.clone()
                        })),
                    }],
                }
                .parse(env, bvars, state, expected_sort)
            }
            ast::Operation::Iff => match state.get_realm() {
                Realm::Evaluated => parse_application(
                    env,
                    &self.span,
                    state,
                    bvars,
                    expected_sort,
                    &IFF_CACHE(),
                    &self.terms,
                ),
                Realm::Symbolic => Self {
                    operation: ast::Operation::And,
                    span: self.span,
                    terms: as_pair_of_term(
                        self.span,
                        self.operation,
                        self.terms.iter().tuple_windows(),
                    ),
                }
                .parse(env, bvars, state, expected_sort),
            },
            ast::Operation::Implies => {
                let function = match state.get_realm() {
                    Realm::Symbolic => IMPLIES_TA_CACHE(),
                    Realm::Evaluated => IMPLIES_CACHE(),
                };
                parse_application(
                    env,
                    &self.span,
                    state,
                    bvars,
                    expected_sort,
                    &function,
                    &self.terms,
                )
            }
            ast::Operation::Or | ast::Operation::And => {
                let realm = state.get_realm();
                let function = match (realm, self.operation) {
                    (Realm::Symbolic, ast::Operation::And) => AND_TA_CACHE(),
                    (Realm::Symbolic, ast::Operation::Or) => OR_TA_CACHE(),
                    (Realm::Evaluated, ast::Operation::And) => AND_CACHE(),
                    (Realm::Evaluated, ast::Operation::Or) => OR_CACHE(),
                    _ => unreachable!(),
                };

                match realm {
                    Realm::Evaluated => parse_application(
                        env,
                        &self.span,
                        state,
                        bvars,
                        expected_sort,
                        &function,
                        &self.terms,
                    ),
                    Realm::Symbolic => {
                        let mut iter = self.terms.iter();
                        let first =
                            iter.next()
                                .unwrap()
                                .parse(env, bvars, state, expected_sort.clone())?; // can't fail
                        iter.try_fold(first, |acc, t| {
                            Ok(function
                                .get_function()
                                .f_a([acc, t.parse(env, bvars, state, expected_sort.clone())?]))
                        })
                    }
                }
            }
        }
    }
}

fn as_pair_of_term<'a, 'b: 'a>(
    span: pest::Span<'b>,
    op: ast::Operation,
    iter: impl IntoIterator<Item = (&'a Term<'b>, &'a Term<'b>)>,
) -> Vec<Term<'b>> {
    iter.into_iter()
        .map(|(a, b)| ast::Term {
            span,
            inner: ast::InnerTerm::Infix(Box::new(ast::Infix {
                operation: op,
                span,
                terms: vec![a.clone(), b.clone()],
            })),
        })
        .collect()
}

impl<'a, 'bump> Parsable<'bump, 'a> for ast::Term<'a> {
    type R = ARichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        if cfg!(debug_assertions) {
            if bvars.iter().map(|(_, v)| v.id).unique().count() != bvars.len() {
                panic!(
                    "there are duplicates:\n\t[{}]",
                    bvars.iter().map(|(_, v)| v).join(", ")
                )
            }
        }

        match_as_trait!(ast::InnerTerm, |x| in &self.inner => LetIn | If | Fndst | Quant | Application | Infix | Macro
                    {x.parse(env, bvars, state, expected_sort)})
    }
}

fn check_out_sort<'str, 'bump>(
    env: &Environement<'bump, 'str>,
    span: Span<'str>,
    realm: &impl KnowsRealm,
    expected_sort: Option<SortProxy<'bump>>,
    out_sort: Option<SortProxy<'bump>>,
    mut forumla: ARichFormula<'bump>,
) -> Result<ARichFormula<'bump>, E> {
    match (out_sort, expected_sort) {
        (None, _) | (_, None) => Ok(forumla),
        (Some(os), Some(es)) => match os.as_option() {
            None => {
                os.unify(&es, realm).unwrap_display(); // should never fail
                Ok(forumla)
            }
            Some(os) => {
                let mut out = os;
                if out == NAME.as_sort() {
                    out = MESSAGE.as_sort();
                    forumla = env.name_caster_collection.cast(MESSAGE.as_sort(), forumla);
                    trace!("name cast in: {}", &forumla);
                }
                if realm.get_realm() == Realm::Evaluated && out.realm() == Some(Realm::Symbolic) {
                    forumla = env.evaluator.get_eval_function(out).unwrap().f_a([forumla]);
                    out = out.maybe_evaluated_sort().unwrap();
                    trace!("evalluation in: {}", &forumla);
                }
                es.unify_rev(&out.into(), realm)
                    .into_rr(span)
                    .debug_continue()?;
                Ok(forumla)
            }
        },
    }
}
