use std::cmp::Ordering;
use std::fmt::Debug;

use hashbrown::HashSet;
use itertools::{Itertools, chain, izip};
use utils::all_or_one::AoOV;
use utils::mdo;
use utils::monad::Monad;
use utils::string_ref::StrRef;

use super::ast_convertion::ToAst;
use super::{Context, RAoO};
use crate::bail_at;
use crate::parser::ast::{self, Application, Order, OrderOperation, QuantifierKind};
use crate::squirrel::Sanitizable;
use crate::squirrel::json::action::{AT, Item, Shape};
use crate::squirrel::json::{self};

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
        .filter(|x| !x.is_init())
        .tuple_combinations()
        .map(move |(a, b)| match mk_depends_lemma(a, b, ctx)? {
            Some(l) => Ok(Some(l)),
            None => mk_mutex_lemma(a, b, ctx),
        })
        .filter_map(Result::transpose)
        .map(|x| RAoO::pure(x?))
}

// copied for squirrel with some optimisation

#[allow(clippy::upper_case_acronyms)] // FIXME: figure out what AT is supposed to mean
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
        } else if izip!(a.iter(), b.iter()).all(|(a, b)| a == b) {
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
/// Wrapper arround [MAT]'s [PartialOrd]. Returns `Some(true)` when `a` strictly depends on `b`,
/// `Some(false)` when `b` strictly depends on `a` and `None` in any other situation
fn depends<A: Eq + Debug>(a: &AT<A>, b: &AT<A>) -> Option<bool> {
    match PartialOrd::partial_cmp(&MAT(a), &MAT(b))? {
        Ordering::Less => Some(true),
        Ordering::Equal => None,
        Ordering::Greater => Some(false),
    }
}

fn mk_depends_lemma<'a>(
    a: &json::Action<'a>,
    b: &json::Action<'a>,
    ctx: Context<'_, 'a>,
) -> crate::Result<Option<ast::Order<'a, StrRef<'a>>>> {
    let cmp = depends(&a.action, &b.action);

    let (a, b) = match cmp {
        // flip to be in the same order
        None => return Ok(None),
        Some(true) => (a, b),
        Some(false) => (b, a),
    };
    if b.indices.len() < a.indices.len() {
        let err_msg = "b has to few indices, this contradicts an implicit requirement of \
                       squirrel's `Lemma.mk_depends_lemma`";
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
        let t1 = Application::new_app(Default::default(), a.name.sanitized(&ctx), idx_a.clone()).into();
        let t2 = Application::new_app(Default::default(), b.name.sanitized(&ctx), idx_b.clone()).into();
        let span = Default::default();
        let options = Default::default();
        let guard = None;
        pure Some(Order { span, quantifier, args: args.into_iter().collect(), t1, t2, kind, options, guard})
    }.owned_get(0))
}

// TODO: optimise
fn mutex_commun_vars(a: &Shape, b: &Shape) -> Option<usize> {
    fn aux(a: &[Item<usize>], b: &[Item<usize>]) -> Option<usize> {
        match (a.split_first(), b.split_first()) {
            (Some((hda, tla)), Some((hdb, tlb))) => {
                if hda == hdb {
                    Some(hda.par_choice.1 + hda.sum_choice.1 + aux(tla, tlb)?)
                } else if hda.par_choice == hdb.par_choice && hda.sum_choice.0 != hdb.sum_choice.0 {
                    // trace!("{a:?} --- {b:?}");
                    Some(hda.par_choice.1)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    aux(a.as_ref(), b.as_ref())
}

fn mk_mutex_lemma<'a>(
    a: &json::Action<'a>,
    b: &json::Action<'a>,
    ctx: Context<'_, 'a>,
) -> crate::Result<Option<ast::Order<'a, StrRef<'a>>>> {
    // if !mutex(a.shape().as_ref(), b.shape().as_ref()) {
    //     return Ok(None);
    // }
    let i_commun = match mutex_commun_vars(&a.shape(), &b.shape()) {
        Some(i) => i,
        _ => return Ok(None),
    };

    assert!(!(a == b && (a.indices().len() == i_commun)));

    let var_commun = &a.indices()[..i_commun];
    // .split_at_checked(i_commun)
    // .ok_or_else(|| err_at!(@ "not enough variable in step {}", a.name().sanitized(&ctx)))?;

    // ensure there are no clashes in variables names
    let other_b = {
        let (_, others_b) = b.indices().split_at(i_commun);
        // .ok_or_else(|| err_at!(@ "not enough variable in step {}", b.name().sanitized(&ctx)))?;

        let mut names: HashSet<_> = a
            .indices()
            .iter()
            .map(|v| v.original_name().clone())
            .collect();
        others_b.iter().map(move |v| {
            let mut v = v.clone();
            let oname = v.original_name_mut();
            while names.contains(oname) {
                *oname = StrRef::new_owned(format!("{oname}_u")).unwrap();
            }
            names.insert(oname.clone());
            v
        })
    }
    .collect_vec();

    let args: Vec<_> = chain!(a.indices.iter(), other_b.iter())
        .map(|var| {
            mdo! {
                let! sort = var.sort().convert(ctx);
                pure (var.sanitized(&ctx), sort)
            }
        })
        .try_collect()?;
    // let [idx_a, idx_b] = [a, b].map(|x| {
    //     x.indices
    //         .iter()
    //         .map(|v| Application::from(v.sanitized(&ctx)).into())
    //         .collect_vec()
    // });
    let idx_a = a
        .indices()
        .iter()
        .map(|v| Application::from(v.sanitized(&ctx)).into())
        .collect_vec();
    let idx_b = chain!(var_commun.iter(), other_b.iter())
        .map(|v| Application::from(v.sanitized(&ctx)).into())
        .collect_vec();

    Ok(mdo!{
        let! args = AoOV::transpose_iter(args);
        let quantifier = QuantifierKind::Forall;
        let kind = OrderOperation::Incompatible;
        let t1 = Application::new_app(Default::default(), a.name.sanitized(&ctx), idx_a.clone()).into();
        let t2 = Application::new_app(Default::default(), b.name.sanitized(&ctx), idx_b.clone()).into();
        let span = Default::default();
        let options = Default::default();
        let guard = None;
        pure Some(Order { span, quantifier, args: args.into_iter().collect(), t1, t2, kind, options, guard})
    }.owned_get(0))
}
