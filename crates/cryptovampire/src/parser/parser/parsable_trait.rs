use std::{borrow::Borrow, fmt::Display, ops::Deref, sync::Arc};
mod cached_builtins;

use anyhow::Context;
use itertools::Itertools;
use log::{log_enabled, trace, warn};

use crate::{
    parser::{
        ast::{self, extra::SnN, LetIn, Term},
        parser::parsing_environement::get_function_mow,
         Pstr,
    },
};
use crate::{
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
        manipulation::OneVarSubstF,
        sort::{
            builtins::{BOOL, CONDITION, MESSAGE, NAME, STEP},
            sort_proxy::SortProxy,
        },
        utils::Applicable,
        variable::{from_usize, uvar, Variable},
    },
    CVResult, CVContext
};
use utils::{f, implvec, match_as_trait, string_ref::StrRef, traits::NicerError};

pub(crate) use self::cached_builtins::*;

use super::{
    parsing_environement::{get_sort, FunctionCache},
    Environement,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct VarProxy<'bump> {
    id: uvar,
    sort: SortProxy<'bump>,
}

impl<'bump> VarProxy<'bump> {
    #[allow(dead_code)]
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

pub trait Parsable<'bump, 'str, L> {
    type R;
    type S;
    /// parse [self] into [Parsable::R].
    ///
    /// ## arguments
    ///  - `env`: the [Environement] used to extract all the information about
    ///     what's already been parsed / partially parsed. It is not used as
    ///     a [KnowsRealm].
    ///  - `bvar`: the currenlty bounded variables. The contract is to leave
    ///     as it was found, that is the caller may modify `bvar` but it has
    ///     to revert it to its old state.
    ///     
    ///     **NB**: there is one notable exception to this rule which is
    ///             [VariableBinding] which add its returned [Variable] to
    ///             `bvar`
    ///  - `state`: the [KnowsRealm]
    ///  - `expected_sort`: the sort that is expected. Set to [None] if we don't
    ///     expect any sort. It also is a [SortProxy] therefore we can use it to
    ///     unify sorts (useful for things like equalities).
    fn parse(
        &self,
        env: &Environement<'bump, 'str, Self::S>,
        bvars: &mut Vec<(Self::S, VarProxy<'bump>)>,
        state: &impl KnowsRealm, // State<'_, 'str, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L>;
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::LetIn<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    #[allow(unreachable_code)]
    #[allow(unused_assignments)]
    fn parse(
        &self,
        env: &Environement<'bump, 'a, Self::S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        let LetIn {
            span: _,
            var,
            t1,
            t2,
        } = self;
        let var = var.parse(env, bvars, state, None)?;
        let t1 = t1.parse(env, bvars, state, Some(var.sort().into()))?;
        let t2 = t2.parse(env, bvars, state, expected_sort)?;

        Ok(t2.apply_substitution2(&OneVarSubstF::new(var, t1)))
    }
}
impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::IfThenElse<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        // generate the expected sorts
        let (es_condition, es_branches): (SortProxy, Option<SortProxy>) = match state.get_realm() {
            Realm::Evaluated => (BOOL.as_sort().into(), expected_sort),
            Realm::Symbolic => (CONDITION.as_sort().into(), Some(MESSAGE.as_sort().into())),
        };

        // check sort
        // if let Some(es) = &expected_sort {
        //     es_branches.unify(es, &state).with_location(&self.span).debug_continue()?;
        // }

        let ast::IfThenElse {
            condition,
            left,
            right,
            ..
        } = self;

        // parse the argumeents
        let condition = condition
            .parse(env, bvars, state, Some(es_condition))
            .debug_continue()?;
        let left = left
            .parse(env, bvars, state, es_branches.clone())
            .debug_continue()?;
        let right = right
            .parse(env, bvars, state, es_branches)
            .debug_continue()?;

        Ok(match state.get_realm() {
            Realm::Evaluated => IF_THEN_ELSE.clone(),
            Realm::Symbolic => IF_THEN_ELSE_TA.clone(),
        }
        .f([condition, left, right]))
    }
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::FindSuchThat<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        expected_sort
            .into_iter()
            .try_for_each(|s| {
                s.expects(MESSAGE.as_sort(), &state)
                    .with_location(&self.span)
            })
            .debug_continue()?;

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
        let vars: Result<Vec<_>, InputError> = vars
            .bindings
            .iter()
            .map(|v| Parsable::parse(v, env, bvars, state, None))
            .collect();
        let vars = vars?;

        // parse the rest
        let condition = condition
            .parse(
                env,
                bvars,
                &Realm::Symbolic,
                Some(CONDITION.as_sort().into()),
            )
            .debug_continue()?;
        let left = left
            .parse(env, bvars, &Realm::Symbolic, Some(MESSAGE.as_sort().into()))
            .debug_continue()?;

        // remove variables
        bvars.truncate(bn);

        let (f /* the function */, fvars /* the free vars */) =
            Function::new_find_such_that(env.container, vars, condition, left, right);

        let ret = f.f(fvars.iter());
        Ok(match state.get_realm() {
            Realm::Symbolic => ret,
            _ => env.evaluator.eval(ret),
        })
    }
}
impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::VariableBinding<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = Variable<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, Self::S>,
        bvars: &mut Vec<(Self::S, VarProxy<'bump>)>,
        realm: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        let ast::VariableBinding {
            variable,
            type_name,
            ..
        } = self;

        if env.functions.contains_key(variable.name().borrow())
            || bvars.iter().map(|(n, _)| n).contains(&variable.name())
        {
            if env.allow_shadowing() {
                warn!("the name {} is already taken, shadowing", variable.name())
            } else {
                bail_at!(
                    variable.0.span,
                    "the name {} is already taken",
                    variable.name()
                )
            }
        }
        let SnN { span, name } = type_name.into();
        let sort = {
            // get the sort, possibly changing it depending on the realm
            let sort = get_sort(env, *span, name)?;
            // if realm.is_evaluated_realm() && false{
            //     sort.maybe_evaluated_sort().unwrap_or(sort)
            // } else {
            //     sort
            // }
            // FIXME: things seem to go wrong with the realm here...
            sort
        };
        if let Some(e) = expected_sort {
            // check if it is what we expected / unify it
            e.expects(sort, realm).with_location(span)?;
        }

        let var = Variable {
            id: from_usize(bvars.len()),
            sort,
        };

        let content = (variable.name().clone(), var.into());
        bvars.push(content); // add it to bvars
        Ok(var)
    }
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::Quantifier<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
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
            .try_for_each(|s| s.expects(es, &state).with_location(span).debug_continue())?;

        let bn = bvars.len();

        // bind the variables
        bvars.reserve(vars.into_iter().len());
        let vars: Result<Vec<_>, InputError> = vars
            .into_iter()
            .map(|v| Parsable::parse(v, env, bvars, state, None))
            .collect();
        let vars = vars?.into();

        // parse body
        let content = content.parse(env, bvars, state, Some(es.into()))?;

        // remove bounded variables from pile
        bvars.truncate(bn);

        let q = {
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

                fq.f(args)
            }
        })
    }
}
impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::Application<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        trace!("parsing {self}");
        match self {
            ast::Application::ConstVar { span, content } => {
                // check if it is a variable
                bvars
                    .iter()
                    .find(|(s, _)| s == content)
                    .map(|(_, v)| {
                        let VarProxy { id, sort } = v;

                        if sort.is_sort(NAME.as_sort()) {
                            bail_at!(
                                span,
                                "assertions with variables of sort Name have a debatable soundness"
                            )
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
                                    .f([Variable { id: *id, sort }]);

                                expected_sort
                                    .as_ref()
                                    .map(|es| es.matches(s, &r))
                                    .transpose()
                                    .with_location(span)
                                    .debug_continue()
                                    .map(|_| formula)
                            }
                            (_, r) => expected_sort
                                .as_ref()
                                .map(|es| es.unify_rev(sort, &r).with_location(span))
                                .unwrap_or_else(|| {
                                    sort.as_option().ok_or(span.err_with(|| "can't infer sort"))
                                })
                                .debug_continue()
                                .map(|sort| Variable { id: *id, sort }.into()),
                        }
                    })
                    // otherwise look for a function
                    .unwrap_or_else(|| {
                        get_function_mow(content, state, env, span)
                            .debug_continue()
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
                                .debug_continue()
                            })
                    })
            }
            ast::Application::Application {
                span,
                function,
                args,
            } => {
                let content = function.name();
                get_function_mow(content, state, env, span).and_then(|f| {
                    parse_application(env, span, state, bvars, expected_sort, f.borrow(), args)
                        .debug_continue()
                })
            }
        }
    }
}

/// parse a function application (when we know it is definitly a function and not a variable)
fn parse_application<'b, 'a, 'bump, S, L>(
    env: &'b Environement<'bump, 'a, S>,
    span: &'b L,
    state: &impl KnowsRealm,
    bvars: &'b mut Vec<(S, VarProxy<'bump>)>,
    expected_sort: Option<SortProxy<'bump>>,
    function: &FunctionCache<'a, 'bump, L, S>,
    args: implvec!(&'b ast::Term<L, S>),
) -> CVResult<ARichFormula<'bump, L>>
where
    S: Pstr,
    for<'c> StrRef<'c>: From<&'c S>,
{
    let signature = function.signature();
    let mut formula_realm = signature.realm();

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
            .map(|(es, t)| t.parse(env, bvars, &state, Some(es)).debug_continue())
            .collect()
    };
    let n_args = n_args?;

    // check arity
    if !signature.args_size().contains(&n_args.len().into()) {
        let range = signature.args_size();
        bail_at!(
            span,
            "wrong number of arguments: got {}, expected [{}, {}]",
            n_args.len(),
            range.start(),
            range.end()
        )
    }

    let ifun = function.get_function();
    // if it's a name, cast it
    let formula = if let Some(name) = ifun.as_name() {
        // assert!(is_name);
        formula_realm = Some(Realm::Symbolic); // names are symbolic
        env.name_caster_collection
            .cast(name.target(), ifun.f(n_args))
    } else {
        ifun.f(n_args)
    };
    // if we are in evaluated land, evaluate
    let formula = match (state.get_realm(), formula_realm) {
        (Realm::Evaluated, Some(Realm::Symbolic)) => env.evaluator.try_eval(formula).unwrap(),
        _ => formula,
    };

    // check output sort
    let out_sort = {
        let mut out_sort = signature.out();
        if out_sort.is_sort(NAME.as_sort()) {
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
        .with_location(span)
        .debug_continue()?;

    Ok(formula)
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::AppMacro<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        let Self {
            span: main_span,
            inner,
        } = self;

        match inner {
            ast::InnerAppMacro::Msg(app) | ast::InnerAppMacro::Cond(app) => {
                let step_as_term = app.parse(env, bvars, state, Some(STEP.as_sort().into()))?;

                let args = if let RichFormula::Fun(_, args) = step_as_term.as_ref() {
                    args
                } else {
                    bail_at!(app.span(), "this can only be a plain reference to a step (not just a term of sort {}))", STEP.name())
                };

                let step_cache = env
                    .functions
                    .get(app.name().borrow())
                    .and_then(|fc| fc.as_step())
                    .with_context(|| f!("{} is not a known step name", app.name()))
                    .with_location(&app.name_span())
                    .debug_continue()?;

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
                    .get(name.name().borrow())
                    .with_context(|| f!("{} is not a known macro", name.name()))
                    .with_location(name.span())
                    .debug_continue()?;

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
                            .debug_continue()
                        })
                        .try_collect()?
                } else {
                    bail_at!(
                        main_span,
                        "not enough arguments: expected {}, got {}",
                        mmacro.args.len(),
                        args.len(),
                    )
                };

                let term = {
                    let mut bvars = mmacro
                        .args
                        .iter()
                        .zip(mmacro.args_name.iter())
                        .zip(0..)
                        .map(|((var_sort, var_name), id)| {
                            (var_name.clone(), Variable::new(id, *var_sort).into())
                        })
                        .collect_vec();
                    mmacro
                        .content
                        .parse(env, &mut bvars, state, expected_sort)
                        .debug_continue()
                }?;

                Ok(term
                    .owned_into_inner()
                    .apply_substitution(0..from_usize(mmacro.args.len()), &args)
                    .into())
            }
        }
    }
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::Infix<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
        trace!("parsing {self}");
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
                )
                .debug_continue(),
                _ => Self {
                    operation: ast::Operation::And,
                    span: self.span,
                    terms: as_pair_of_term(
                        self.span,
                        self.operation,
                        self.terms.iter().tuple_windows(),
                    ),
                }
                .parse(env, bvars, state, expected_sort)
                .debug_continue(),
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
                )
                .debug_continue(),
                Realm::Symbolic => Self {
                    operation: ast::Operation::HardEq,
                    ..self.clone()
                }
                .parse(env, bvars, state, expected_sort)
                .debug_continue(),
            },
            ast::Operation::Neq => ast::Application::Application {
                span: self.span,
                function: ast::Function(ast::Sub {
                    span: self.span,
                    content: ast::Ident {
                        span: self.span,
                        content: S::from_static("not"),
                    },
                }),
                args: vec![ast::Term {
                    span: self.span,
                    inner: ast::InnerTerm::Infix(Arc::new(Self {
                        operation: ast::Operation::Eq,
                        ..self.clone()
                    })),
                }],
            }
            .parse(env, bvars, state, expected_sort)
            .debug_continue(),
            ast::Operation::Iff => match state.get_realm() {
                Realm::Evaluated => parse_application(
                    env,
                    &self.span,
                    state,
                    bvars,
                    expected_sort,
                    &EQUALITY_CACHE(),
                    &self.terms,
                )
                .debug_continue(),
                Realm::Symbolic => Self {
                    operation: ast::Operation::And,
                    span: self.span,
                    terms: as_pair_of_term(
                        self.span,
                        self.operation,
                        self.terms.iter().tuple_windows(),
                    ),
                }
                .parse(env, bvars, state, expected_sort)
                .debug_continue(),
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
                .debug_continue()
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
                        let first = iter
                            .next()
                            .unwrap() // can't fail
                            .parse(env, bvars, state, expected_sort.clone())
                            .debug_continue()?;
                        iter.try_fold(first, |acc, t| {
                            Ok(function.get_function().f([
                                acc,
                                t.parse(env, bvars, state, expected_sort.clone())
                                    .debug_continue()?,
                            ]))
                        })
                    }
                }
            }
        }
        .debug_continue()
    }
}

fn as_pair_of_term<'a, 'b: 'a, S>(
    span: Location<'b>,
    op: ast::Operation,
    iter: impl IntoIterator<Item = (&'a Term<'b, S>, &'a Term<'b, S>)>,
) -> Vec<Term<'b, S>>
where
    S: Pstr + 'a,
    for<'c> StrRef<'c>: From<&'c S>,
{
    iter.into_iter()
        .map(|(a, b)| ast::Term {
            span,
            inner: ast::InnerTerm::Infix(Arc::new(ast::Infix {
                operation: op,
                span,
                terms: vec![a.clone(), b.clone()],
            })),
        })
        .collect()
}

impl<'a, 'bump, S, L> Parsable<'bump, 'a, L> for ast::Term<L, S>
where
    S: Pstr,
    for<'b> StrRef<'b>: From<&'b S>,
{
    type R = ARichFormula<'bump>;
    type S = S;

    fn parse(
        &self,
        env: &Environement<'bump, 'a, S>,
        bvars: &mut Vec<(S, VarProxy<'bump>)>,
        state: &impl KnowsRealm,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> CVResult<Self::R, L> {
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
