// FIXME: do it better
pub const DEFAULT_TUPLE_NAME: StrRef<'static> = StrRef::from_static("_$tuple");
pub const DEFAULT_FST_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$fst");
pub const DEFAULT_SND_PROJ_NAME: StrRef<'static> = StrRef::from_static("_$snd");

use cryptovampire_lib::formula::sort::builtins::{BOOL, MESSAGE, STEP};
use itertools::{chain, izip, Itertools};
use utils::{
    all_or_one::{AllOrOneShape, AoOV},
    implvec, mdo,
    monad::Monad,
    pure,
    string_ref::StrRef,
};

use crate::{
    bail_at, err_at,
    parser::{
        ast::{self, Options},
        Location,
    },
    squirrel::json::{self, Named, Pathed, ProcessedSquirrelDump},
};

use super::{helper_functions::*, RAoO};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Context<'a, 'str> {
    pub shape: AllOrOneShape,
    pub dump: &'a ProcessedSquirrelDump<'str>,
}

impl<'a, 'str> Context<'a, 'str> {
    pub fn new(dump: &'a ProcessedSquirrelDump<'str>) -> Self {
        Self {
            shape: AllOrOneShape::Any(()),
            dump,
        }
    }

    pub fn dump(&self) -> &ProcessedSquirrelDump<'str> {
        self.dump
    }

    pub fn shape(&self) -> AllOrOneShape {
        self.shape
    }
}

pub trait ToAst<'a> {
    type Target;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target>;
}

impl<'a> ToAst<'a> for json::Term<'a> {
    type Target = ast::Term<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Term::Fun { .. } => {
                bail_at!(@ "no high order")
            }
            json::Term::Let { .. } => bail_at!(@ "no lets"),
            // actual work
            json::Term::Var { var } => {
                mdo!(pure ast::Application::from(var.name().drop_guard()).into())
            }
            json::Term::Tuple { elements } => convert_tuple(elements, ctx),
            json::Term::Quant {
                quantificator,
                vars,
                body,
            } => convert_quantifier(quantificator, vars, body, ctx),
            json::Term::Find {
                vars,
                condition,
                success,
                faillure,
            } => convert_findst(vars, condition, success, faillure, ctx),
            json::Term::Proj { id, body } => convert_projection(*id, body, ctx),
            json::Term::Diff { terms } => convert_diff(terms, ctx),
            json::Term::App { f, args } => convert_application(f, args, ctx),
            json::Term::Name { symb, args } => convert_name_application(symb, args, ctx),
            json::Term::Macro {
                symb,
                args,
                timestamp,
            } => convert_macro_application(symb, args, timestamp, ctx),
            json::Term::Action { symb, args } => convert_action_application(symb, args, ctx),
        }
    }
}

impl<'a> ToAst<'a> for json::sort::Type<'a> {
    type Target = ast::TypeName<'a, StrRef<'a>>;

    fn convert<'b>(&self, _: Context<'b, 'a>) -> RAoO<Self::Target> {
        match self {
            json::Type::Message => mdo!(pure MESSAGE.name().into()),
            json::Type::Boolean => mdo!(pure BOOL.name().into()),
            json::Type::Timestamp => mdo!(pure STEP.name().into()),
            json::Type::Index => mdo!(pure StrRef::from_static("index").into()),
            json::Type::TBase(p) => mdo!(pure p.equiv_name_ref().into()),
            json::Type::TVar { .. }
            | json::Type::TUnivar { .. }
            | json::Type::Tuple { .. }
            | json::Type::Fun { .. } => Err(err_at!(@ "arg")),
        }
    }
}

impl<'a> ToAst<'a> for json::Action<'a> {
    type Target = ast::Step<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        let Self {
            name,
            indices,
            condition,
            updates,
            output,
            action: _,
            input: _,
            globals: _,
        } = self;

        let name = ast::StepName::from(name.equiv_name_ref());
        let args: Vec<_> = indices
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort.convert(ctx);
                    pure (var.id.name().drop_guard(), sort)
                }
            })
            .try_collect()?;
        let assignements: Vec<_> = updates.iter().map(|upd| upd.convert(ctx)).try_collect()?;

        let options = Options::default();

        // FIXME: make this work
        assert!(
            condition.vars.is_empty(),
            "free variables in a condition (and I'm not sure what this means)"
        );

        mdo! {
            let! message = output.term.convert(ctx);
            let! condition = condition.term.convert(ctx);
            let! assignements = Ok(AoOV::transpose(assignements.clone()));
            let! args = Ok(AoOV::transpose(args.clone()));
            pure ast::Step {
                name: name.clone(),
                span: Default::default(),
                args: args.into_iter().collect(),
                condition: condition.clone(),
                message: message.clone(),
                assignements: Some(assignements.iter().cloned().collect()),
                options: options.clone()
            }
        }
    }
}

impl<'a> ToAst<'a> for json::action::Update<'a> {
    type Target = ast::Assignement<'a, StrRef<'a>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        let Self { symb, args, body } = self;

        // let cell = apply_fun(symb.clone(), args, ctx)?;
        let args: Vec<_> = args.iter().map(|arg| arg.convert(ctx)).try_collect()?;
        mdo! {
            let! args = Ok(AoOV::transpose(args));
            let! term = body.convert(ctx);
            pure ast::Assignement {
                span: Default::default(),
                cell: ast::Application::new_app(symb.clone().drop_guard(), args.clone()),
                term,
                fresh_vars: None
            }
        }
    }
}

impl<'a> ToAst<'a> for json::Macro<'a> {
    type Target = Option<ast::Macro<'a, StrRef<'a>>>;

    fn convert<'b>(&self, ctx: Context<'b, 'a>) -> RAoO<Self::Target> {
        use json::mmacro::*;
        let json::Content { symb, data } = self;
        match data {
            Data::Global(GlobalMacro {
                arity: _,
                sort: _,
                data:
                    GlobalData {
                        inputs,
                        indices,
                        ts,
                        body,
                        action: _,
                        ty: _,
                    },
            }) => {
                let args: Vec<_> = chain!(indices.iter(), inputs.iter(), [ts])
                    .map(|var| {
                        mdo! {
                            let! sort = var.sort.convert(ctx);
                            pure (var.id.name().drop_guard(), sort)
                        }
                    })
                    .try_collect()?;
                mdo! {
                    let! args = Ok(AoOV::transpose(args));
                    let! term = body.convert(ctx);
                    pure Some(ast::Macro {
                        span: Location::default(),
                        name: symb.equiv_name_ref().into(),
                        args:args.iter().cloned().collect(),
                        term,
                        options: Options::default()
                    })
                }
            }
            _ => pure!(None),
        }
    }
}

mod convert_order {
    use super::{Context, ToAst};
    use std::{cmp::Ordering, fmt::Debug, process::id};
    use utils::{monad::Monad, pure};

    use itertools::{izip, Itertools};
    use utils::{all_or_one::AoOV, mdo, string_ref::StrRef};

    use crate::{
        bail_at,
        parser::{
            ast::{self, Application, InnerTerm, Order, OrderOperation, QuantifierKind},
            InputError,
        },
        squirrel::json::{self, action::AT, Named, Pathed},
    };

    pub fn mk_depends_mutex_lemmas<'a, 'b, I>(
        steps: I,
        ctx: Context<'b, 'a>,
    ) -> Result<Vec<ast::Order<'a, StrRef<'a>>>, InputError>
    where
        I: IntoIterator<Item = &'b json::Action<'a>>,
        I::IntoIter: Clone,
        'a: 'b,
    {
        steps
            .into_iter()
            .tuple_combinations()
            .map(|(a, b)| match mk_depends_lemma(a, b, ctx)? {
                Some(l) => Ok(Some(l)),
                None => mk_mutex_lemma(a, b, ctx),
            })
            .filter_map(Result::transpose)
            .collect()
    }

    // copied for squirrel with some optimisation

    #[derive(Debug, PartialEq)]
    struct MAT<'a, A>(&'a json::action::AT<A>);

    impl<'a, A: PartialEq + Debug> PartialOrd for MAT<'a, A> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            let a = self;
            let b = other;
            if PartialEq::eq(a, b) {
                Some(Ordering::Equal)
            } else {
                if izip!(a.0.iter(), b.0.iter()).all(|(a, b)| a == b) {
                    if a.0.len() < b.0.len() {
                        Some(Ordering::Less)
                    } else {
                        Some(Ordering::Greater)
                    }
                } else {
                    None
                }
            }
        }
    }
    /// Wrapper arround [MAT]'s [PartialOrd]. Returns `Some(true)` when `a` strictly depends on `b`,
    /// `Some(false)` when `b` strictly depends on `a` and `None` in any other situation
    fn depends<A: Eq + Debug>(a: &AT<A>, b: &AT<A>) -> Option<bool> {
        match PartialOrd::partial_cmp(&MAT(a), &MAT(b))? {
            Ordering::Less => Some(true),
            Ordering::Equal => None,
            Ordering::Greater => Some(false),
        }
    }

    fn mk_depends_lemma<'a, 'b>(
        a: &json::Action<'a>,
        b: &json::Action<'a>,
        ctx: Context<'b, 'a>,
    ) -> Result<Option<ast::Order<'a, StrRef<'a>>>, InputError> {
        let cmp = depends(&a.action, &b.action);

        let (a, b) = match cmp {
            // flip to be in the same order
            None => return Ok(None),
            Some(true) => (a, b),
            Some(false) => (b, a),
        };
        if !(b.indices.len() >= a.indices.len()) {
            let err_msg = "b has to few indices, this contradicts an implicit requirement of squirrel's `Lemma.mk_depends_lemma`";
            bail_at!(@ "{err_msg}")
        }

        let [idx_a, idx_b] = [a, b].map(|x| {
            x.indices
                .iter()
                .map(|v| Application::from(v.name().drop_guard()).into())
                .collect_vec()
        });
        let args: Vec<_> = b
            .indices
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort.convert(ctx);
                    pure (var.id.name().drop_guard(), sort)
                }
            })
            .try_collect()?;

        Ok(mdo!{
            let! args = AoOV::transpose(args);
            let quantifier = QuantifierKind::Forall;
            let kind = OrderOperation::Lt;
            let t1 = Application::new_app(a.name.equiv_name_ref(), idx_a.clone()).into();
            let t2 = Application::new_app(a.name.equiv_name_ref(), idx_b.clone()).into();
            let span = Default::default();
            let options = Default::default();
            let guard = None;
            pure Some(Order { span, quantifier, args: args.into_iter().collect(), t1, t2, kind, options, guard})
        }.owned_get(0))
    }

    fn mutex<A: Eq + Debug>(a: &AT<A>, b: &AT<A>) -> bool {
        a.len() == b.len() && {
            'm: {
                for (a, b) in izip!(a.iter(), b.iter()) {
                    if a.par_choice == b.par_choice {
                        if a.sum_choice == b.sum_choice {
                            continue;
                        } else {
                            break 'm true;
                        }
                    } else {
                        break 'm false;
                    }
                }
                false
            }
        }
    }

    fn mk_mutex_lemma<'a, 'b>(
        a: &json::Action<'a>,
        b: &json::Action<'a>,
        ctx: Context<'b, 'a>,
    ) -> Result<Option<ast::Order<'a, StrRef<'a>>>, InputError> {
        if !mutex(a.shape().as_ref(), b.shape().as_ref()) {
            return Ok(None);
        }

        let args: Vec<_> = b
            .indices
            .iter()
            .map(|var| {
                mdo! {
                    let! sort = var.sort.convert(ctx);
                    pure (var.id.name().drop_guard(), sort)
                }
            })
            .try_collect()?;
        let [idx_a, idx_b] = [a, b].map(|x| {
            x.indices
                .iter()
                .map(|v| Application::from(v.name().drop_guard()).into())
                .collect_vec()
        });

        Ok(mdo!{
            let! args = AoOV::transpose(args);
            let quantifier = QuantifierKind::Forall;
            let kind = OrderOperation::Incompatible;
            let t1 = Application::new_app(a.name.equiv_name_ref(), idx_a.clone()).into();
            let t2 = Application::new_app(a.name.equiv_name_ref(), idx_b.clone()).into();
            let span = Default::default();
            let options = Default::default();
            let guard = None;
            pure Some(Order { span, quantifier, args: args.into_iter().collect(), t1, t2, kind, options, guard})
        }.owned_get(0))
    }
}
pub use convert_order::mk_depends_mutex_lemmas;
