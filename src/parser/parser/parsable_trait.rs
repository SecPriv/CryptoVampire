
use itertools::Itertools;

use crate::{
    environement::traits::{KnowsRealm, Realm},
    f,
    formula::{
        self,
        formula::RichFormula,
        function::{
            self,
            builtin::{IF_THEN_ELSE, IF_THEN_ELSE_TA, INPUT},
            inner::term_algebra::TermAlgebra,
            signature::{Signature},
            traits::MaybeEvaluatable,
            Function,
        },
        sort::{
            builtins::{BOOL, CONDITION, MESSAGE, STEP},
            sort_proxy::{SortProxy},
            Sort,
        },
        variable::Variable,
    },
    implvec, match_as_trait,
    parser::{
        ast::{self, extra::SnN, VariableBinding},
        err, merr, IntoRuleResult, E,
    },
};

use super::{
    parsing_environement::{get_function, get_sort},
    state::State,
    Environement,
};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct VarProxy<'bump> {
    id: usize,
    sort: SortProxy<'bump>,
}

impl<'bump> From<Variable<'bump>> for VarProxy<'bump> {
    fn from(value: Variable<'bump>) -> Self {
        Self {
            id: value.id,
            sort: value.sort.into(),
        }
    }
}

pub trait Parsable<'bump, 'str>
where
    'bump: 'str,
{
    type R;
    fn parse(
        &self,
        env: &Environement<'bump, 'str>,
        bvars: &mut Vec<(&'str str, VarProxy<'bump>)>,
        state: State<'_, 'str, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E>;
}

impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::LetIn<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        // current length of the pile of variable
        // to be reused for variable indexing, and troncating the pile
        let vn = bvars.len();

        // retrieve data
        let ast::LetIn { var, t1, t2, .. } = self;

        // defined a new variable of unknown type
        let v = VarProxy {
            id: vn,
            sort: Default::default(),
        };

        // parse t1 expecting the unknown sort
        let t1 = t1.parse(env, bvars, state, Some(v.sort.clone()))?;

        // parse t2
        let t2 = {
            bvars.push((var.name(), v.clone())); // add var to the pile
            let t2 = t2.parse(env, bvars, state, expected_sort.clone())?;
            bvars.truncate(vn); // remove it from the pile
            t2
        };

        // replace `v` by its content: `t1`
        Ok(t2.apply_substitution([vn], [&t1]))
    }
}
impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::IfThenElse<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        // generate the expected sorts
        let (ec, eb) = match state.get_realm() {
            Realm::Evaluated => (BOOL.as_sort().into(), Default::default()),
            Realm::Symbolic => (CONDITION.as_sort().into(), MESSAGE.as_sort().into()),
        };

        let expected_sort = if let Realm::Symbolic = state.get_realm() {
            Some(MESSAGE.as_sort().into())
        } else {
            expected_sort
        };

        // check sort
        if let Some(e) = expected_sort.and_then(|s| s.into()) {
            SortProxy::expects(&eb, e, &state).into_rr(self.span)?
        }

        let ast::IfThenElse {
            condition,
            left,
            right,
            ..
        } = self;

        let condition = condition.parse(env, bvars, state, Some(ec))?;
        let left = left.parse(env, bvars, state, Some(eb.clone()))?;
        let right = right.parse(env, bvars, state, Some(eb))?;

        Ok(match state.get_realm() {
            Realm::Evaluated => IF_THEN_ELSE.clone(),
            Realm::Symbolic => IF_THEN_ELSE_TA.clone(),
        }
        .f([condition, left, right]))
    }
}

impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::FindSuchThat<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
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
        let right = right.parse(
            env,
            bvars,
            state.to_symbolic(),
            Some(MESSAGE.as_sort().into()),
        )?;

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
                if env.function_hash.contains_key(variable.name()) {
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
            state.to_symbolic(),
            Some(CONDITION.as_sort().into()),
        )?;
        let left = left.parse(
            env,
            bvars,
            state.to_symbolic(),
            Some(MESSAGE.as_sort().into()),
        )?;

        // remove variables
        bvars.truncate(bn);

        let (f /* the function */, fvars /* the free vars */) =
            Function::new_find_such_that(env.container, vars, condition, left, right);

        Ok(match state.get_realm() {
            Realm::Symbolic => f.f(fvars.into_iter().map(RichFormula::from)),
            _ => todo!(),
        })
    }
}
impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Quantifier<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
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
                if env.function_hash.contains_key(vname) {
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
        let vars = vars?;

        // parse body
        let content = content.parse(env, bvars, state, Some(es.into()))?;

        // remove bounded variables from pile
        bvars.truncate(bn);

        let q = {
            let status = match state.get_realm() {
                Realm::Evaluated => formula::quantifier::Status::Bool,
                Realm::Symbolic => formula::quantifier::Status::Condition,
            };
            match kind {
                ast::QuantifierKind::Forall => formula::quantifier::Quantifier::Forall {
                    variables: vars,
                    status,
                },
                ast::QuantifierKind::Exists => formula::quantifier::Quantifier::Exists {
                    variables: vars,
                    status,
                },
            }
        };

        Ok(match state.get_realm() {
            Realm::Evaluated => RichFormula::Quantifier(q, Box::new(content)),
            Realm::Symbolic => {
                let fq =
                    Function::new_quantifier_from_quantifier(env.container, q, Box::new(content));

                let args = match fq.as_inner() {
                    function::InnerFunction::TermAlgebra(TermAlgebra::Quantifier(q)) => {
                        q.free_variables.iter()
                    }
                    _ => unreachable!(),
                }
                .map(RichFormula::from);

                fq.f(args)
            }
        })
    }
}
impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Application<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
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
                        let sort = expected_sort
                            .clone()
                            .map(|es| sort.unify(&es, &state).into_rr(*span))
                            .unwrap_or_else(|| {
                                Into::<Option<Sort>>::into(sort)
                                    .ok_or_else(|| merr(*span, f!("can't infer sort")))
                            })?;

                        Ok(Variable { id: *id, sort }.into())
                    })
                    // otherwise look for a function
                    .unwrap_or_else(|| {
                        get_function(env, *span, *content).and_then(|f| {
                            parse_application(env, span, state, bvars, expected_sort, f, [])
                        })
                    })
            }
            ast::Application::Application {
                span,
                function,
                args,
            } => get_function(env, *span, function.0.content.content)
                .and_then(|f| parse_application(env, span, state, bvars, expected_sort, f, args)),
        }
    }
}

/// parse a function application (when we know it is definitly a function and not a variable)
fn parse_application<'b, 'a, 'bump: 'a>(
    env: &'b Environement<'bump, 'a>,
    span: &'b pest::Span<'a>,
    state: State<'b, 'a, 'bump>,
    bvars: &'b mut Vec<(&'a str, VarProxy<'bump>)>,
    expected_sort: Option<SortProxy<'bump>>,
    function: Function<'bump>,
    args: implvec!(&'b ast::Term<'a>),
) -> Result<RichFormula<'bump>, E> {
    // get the evaluated version if needed
    let f = match state.get_realm() {
        Realm::Evaluated => function
            .as_term_algebra()
            .maybe_get_evaluated()
            .unwrap_or(function),
        Realm::Symbolic => function,
    };

    let signature = function.signature();

    // check output sort
    let _ = expected_sort
        .map(|es| es.unify(&signature.out(), &state))
        .transpose()
        .into_rr(*span)?;

    // parse further
    let n_args: Result<Vec<_>, _> = signature
        .args()
        .into_iter()
        .zip(args.into_iter())
        .map(|(es, t)| t.parse(env, bvars, state, Some(es)))
        .collect();
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

    Ok(f.f(n_args))
}

impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::AppMacro<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        let Self {
            span: main_span,
            inner,
        } = self;

        match inner {
            ast::InnerAppMacro::Msg(app) | ast::InnerAppMacro::Cond(app) => {
                let step_as_term = app.parse(env, bvars, state, Some(STEP.as_sort().into()))?;

                let args = if let RichFormula::Fun(_, args) = &step_as_term {
                    Ok(args)
                } else {
                    err(
                            merr(app.span(), f!("this can only be a plain reference to a step (not just a term of sort {}))", STEP.name()))
                        )
                }?;

                let step = env.step_lut_to_parse.get(app.name()).ok_or_else(|| {
                    merr(
                        app.name_span(),
                        f!("{} is not a known step name", app.name()),
                    )
                })?;

                let nbvars: Result<Vec<_>, _> = step
                    .args
                    .into_iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let name = v.variable.name();
                        let sort = env.sort_hash.get(v.type_name.name()).ok_or_else(|| {
                            merr(
                                v.type_name.name_span(),
                                f!("{} is not a known type", v.type_name.name()),
                            )
                        })?;
                        Ok((
                            name,
                            VarProxy {
                                id: i + 1,
                                sort: sort.into(),
                            },
                        ))
                    })
                    .chain([Ok((
                        "in",
                        VarProxy {
                            id: 0,
                            sort: MESSAGE.as_sort().into(),
                        },
                    ))])
                    .collect();
                let mut nbvars = nbvars?;
                let n = bvars.len();

                let (to_parse, n_es) = match inner {
                    ast::InnerAppMacro::Msg(_) => (&step.message, MESSAGE.as_sort()),
                    ast::InnerAppMacro::Cond(_) => (&step.condition, CONDITION.as_sort()),
                    _ => unreachable!(),
                };
                if let Some(es) = expected_sort {
                    let n_es_2 = SortProxy::from(n_es)
                        .unify(&es, &state)
                        .into_rr(*main_span)?;
                    assert_eq!(n_es, n_es_2);
                };

                let term = to_parse.parse(env, &mut nbvars, state, Some(n_es.into()))?;

                let input = INPUT.f([step_as_term.clone()]);
                Ok(term.apply_substitution(0..=n, [&input].into_iter().chain(args)))
            }
            ast::InnerAppMacro::Other { name, args } => {
                let mmacro = env
                    .macro_hash
                    .get(name.name())
                    .ok_or_else(|| merr(name.span(), f!("{} is not a known macro", name.name())))?;

                let args: Vec<_> = if mmacro.args.len() == args.len() {
                    mmacro
                        .args
                        .iter()
                        .zip(args)
                        .map(|((_, v), arg)| arg.parse(env, bvars, state, Some(v.sort().into())))
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
                        .map(|(s, v)| (*s, (*v).into()))
                        .collect_vec();
                    mmacro.content.parse(env, &mut bvars, state, expected_sort)
                }?;

                Ok(term.apply_substitution(mmacro.args.iter().map(|(_, v)| v.id), &args))
            }
        }
    }
}
impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Infix<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        _env: &Environement<'bump, 'a>,
        _bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        _state: State<'_, 'a, 'bump>,
        _expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        // let n_es = match state {
        //     State::Convert | State::High => BOOL.as_sort().into(),
        //     State::Low => todo!(),
        // };

        todo!()
    }
}
impl<'a, 'bump: 'a> Parsable<'bump, 'a> for ast::Term<'a> {
    type R = RichFormula<'bump>;

    fn parse(
        &self,
        env: &Environement<'bump, 'a>,
        bvars: &mut Vec<(&'a str, VarProxy<'bump>)>,
        state: State<'_, 'a, 'bump>,
        expected_sort: Option<SortProxy<'bump>>,
    ) -> Result<Self::R, E> {
        match_as_trait!(ast::InnerTerm, |x| in &self.inner => LetIn | If | Fndst | Quant | Application | Infix | Macro
                    {x.parse(env, bvars, state, expected_sort)})
    }
}
