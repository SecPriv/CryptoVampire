use super::{ast_convertion::ToAst, Context, RAoO};
use std::{cmp::Ordering, fmt::Debug};
use utils::monad::Monad;

use itertools::{izip, Itertools};
use utils::{all_or_one::AoOV, mdo, string_ref::StrRef};

use crate::{
    bail_at,
    parser::{
        ast::{self, Application, Order, OrderOperation, QuantifierKind},
        InputError,
    },
    squirrel::{
        json::{self, action::AT},
        Sanitizable,
    },
};

/// This is a somewhat dump copy of `Lemma.mk_depends_mutex` in `squirrel`.
/// As this is expection a `squirrel` input this *should* be fine.
///
/// I still don't fully understand what's the format squirrel is giving me
/// and especially what are the invariants. I do believe some edge cases
/// still aren't supported, but I believes this comes from squirrel not
/// supporting them itself.
pub fn mk_depends_mutex_lemmas<'a, 'b, I>(
    steps: I,
    ctx: Context<'b, 'a>,
) -> impl Iterator<Item = RAoO<ast::Order<'a, StrRef<'a>>>> + 'b
where
    I: IntoIterator<Item = &'b json::Action<'a>> + 'b,
    I::IntoIter: Clone,
    'a: 'b,
{
    steps
        .into_iter()
        .tuple_combinations()
        .map(move |(a, b)| match mk_depends_lemma(a, b, ctx)? {
            Some(l) => Ok(Some(l)),
            None => mk_mutex_lemma(a, b, ctx),
        })
        .filter_map(Result::transpose)
        .map(|x| RAoO::pure(x?))
}

// copied for squirrel with some optimisation

#[derive(Debug, PartialEq, Clone, Copy)]
struct MAT<'a, A>(&'a json::action::AT<A>);

impl<'a, A> std::ops::Deref for MAT<'a, A> {
    type Target = json::action::AT<A>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, A: PartialEq + Debug> PartialOrd for MAT<'a, A> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        let a = self;
        let b = other;
        if PartialEq::eq(a, b) {
            Some(Ordering::Equal)
        } else {
            if izip!(a.iter(), b.iter()).all(|(a, b)| a == b) {
                if a.len() < b.len() {
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
            .map(|v| Application::from(v.sanitized(&ctx)).into())
            .collect_vec()
    });
    let args: Vec<_> = b
        .indices
        .iter()
        .map(|var| {
            mdo! {
                let! sort = var.sort().convert(ctx);
                pure (var.sanitized(&ctx), sort)
            }
        })
        .try_collect()?;

    Ok(mdo!{
        let! args = AoOV::transpose_iter(args);
        let quantifier = QuantifierKind::Forall;
        let kind = OrderOperation::Lt;
        let t1 = Application::new_app(a.name.sanitized(&ctx), idx_a.clone()).into();
        let t2 = Application::new_app(a.name.sanitized(&ctx), idx_b.clone()).into();
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
                        // if we are taking the same ctrl flow branch,
                        // we look deeper
                        continue;
                    } else {
                        // if we find an incompatibility, we bail out
                        // with the result
                        break 'm true;
                    }
                } else {
                    // if no incompatibility are found, then we say so
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
                let! sort = var.sort().convert(ctx);
                pure (var.sanitized(&ctx), sort)
            }
        })
        .try_collect()?;
    let [idx_a, idx_b] = [a, b].map(|x| {
        x.indices
            .iter()
            .map(|v| Application::from(v.sanitized(&ctx)).into())
            .collect_vec()
    });

    Ok(mdo!{
        let! args = AoOV::transpose_iter(args);
        let quantifier = QuantifierKind::Forall;
        let kind = OrderOperation::Incompatible;
        let t1 = Application::new_app(a.name.sanitized(&ctx), idx_a.clone()).into();
        let t2 = Application::new_app(a.name.sanitized(&ctx), idx_b.clone()).into();
        let span = Default::default();
        let options = Default::default();
        let guard = None;
        pure Some(Order { span, quantifier, args: args.into_iter().collect(), t1, t2, kind, options, guard})
    }.owned_get(0))
}
