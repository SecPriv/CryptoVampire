use std::collections::VecDeque;

use egg::{Analysis, EGraph, Id, Language, RecExpr};
use itertools::Itertools;
use log::warn;
use quarck::CowArc;
use rustc_hash::FxHashMap;
use utils::{econtinue_if, ereturn_if};

use crate::Lang;
use crate::terms::Formula;

/// partial result for [pull_from_egraph]
///
/// This performs the extraction from the egraph. By the end this will insert a
/// whole closure reachable by `id` into `id_buffer` and `recexpr_buffer` that
/// doesn't use [Function] forbidden by `filter` (i.e., `filter` must return
/// `true` on all functions) or it returns [None]. At all time, if
/// `recexpr_buffer[i]` is `Some(e)` (and is defined) then `e` is an enode of
/// `egraph[id_buffer[i]]`
///
/// ### Other notable points:
/// - the element are not sorted in anyway
/// - all element that are not [None] have their whole closure in
/// - there can be elments
pub(crate) fn inner_generic<'a, N: Analysis<Lang>, F: FnMut(&Lang) -> bool>(
    egraph: &'a EGraph<Lang, N>,
    mut filter: F,
    id: Id,
    id_buffer: &mut Vec<Id>,
    recexpr_buffer: &mut Vec<Option<&'a Lang>>,
) -> Result<(), Id> {
    debug_assert!(!id_buffer.contains(&id));
    debug_assert_eq!(id_buffer.len(), recexpr_buffer.len());
    let eclass = &egraph[id];
    let len = recexpr_buffer.len();
    id_buffer.push(id);
    recexpr_buffer.push(None);

    'enodes: for e in eclass.iter().filter(|x| filter(x)) {
        'children: for cid in Language::children(e) {
            if let Some(i) = id_buffer.iter().position(|id| id == cid) {
                if recexpr_buffer[i].is_some() {
                    continue 'children;
                } else {
                    continue 'enodes;
                }
            }

            econtinue_if!('enodes, inner(egraph, *cid, id_buffer, recexpr_buffer).is_ok());

            if cfg!(debug_assertions) {
                debug_assert_eq!(id_buffer.len(), recexpr_buffer.len());
                let (i, _) = id_buffer.iter().find_position(|x| x == &cid).unwrap();
                assert!(recexpr_buffer[i].is_some())
            }
        }

        // if we reach that point, we can save the result and exit
        recexpr_buffer[len] = Some(e);
        return Ok(());
    }

    // faillure case
    if cfg!(debug_assertions) {
        let e = egraph.id_to_expr(id);
        warn!(
            "{e:} cannot be turned into a non recursive formula without using \"prolog\"-specific \
             functions"
        )
    }
    Err(id)
}

#[derive(Debug, Clone)]
enum ExtractionStatus {
    Looping,
    Empty,
    Found(Formula),
}

impl ExtractionStatus {
    #[must_use]
    fn into_found(self) -> Option<Formula> {
        if let Self::Found(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

impl From<Option<Formula>> for ExtractionStatus {
    fn from(value: Option<Formula>) -> Self {
        match value {
            Some(x) => Self::Found(x),
            None => Self::Empty,
        }
    }
}

fn inner_generic2<N: Analysis<Lang>, F: FnMut(&Lang) -> bool>(
    egraph: &EGraph<Lang, N>,
    filter: &mut F,
    id: Id,
    recexpr_buffer: &mut FxHashMap<Id, ExtractionStatus>,
) -> ExtractionStatus {
    if let Some(status) = recexpr_buffer.get(&id) {
        return status.clone();
    }

    egraph[id]
        .nodes
        .iter() //.filter(|l| filter(*l))
        .filter_map(|l @ Lang { head, args }| {
            filter(l).then_some(())?;
            let args: Option<CowArc<'static, _>> = args
                .iter()
                .copied()
                .map(|id| inner_generic2(egraph, filter, id, recexpr_buffer).into_found())
                .collect();
            Some(Formula::App {
                head: head.clone(),
                args: args?,
            })
        })
        .next()
        .into()
}

/// [pull_from_egraph_inner_generic] which blocks prolog functions
pub(crate) fn inner<'a, N: Analysis<Lang>>(
    egraph: &'a EGraph<Lang, N>,
    id: Id,
    id_buffer: &mut Vec<Id>,
    recexpr_buffer: &mut Vec<Option<&'a Lang>>,
) -> Result<(), Id> {
    inner_generic(
        egraph,
        |f| !f.head.is_prolog_only() || f.head.is_quantifier(),
        id,
        id_buffer,
        recexpr_buffer,
    )
}

pub(crate) fn topo_sort<'a>(ids: &[Id], langs: &[Option<&'a Lang>]) -> (Vec<Id>, Vec<&'a Lang>) {
    debug_assert_eq!(ids.len(), langs.len());
    ereturn_if!(ids.is_empty(), Default::default());

    let mut nids = Vec::with_capacity(ids.len());
    let mut nlangs = Vec::with_capacity(langs.len());

    // let mut visited  = vec![false; langs.len()];
    let mut todo = VecDeque::new();

    todo.push_back(ids.first().unwrap());

    while let Some(id) = todo.pop_front() {
        debug_assert!(!nids.contains(id), "found a cycle");

        let idx = ids.iter().position(|x| x == id).unwrap();
        let Some(l) = langs[idx] else {
            panic!("reached a point outside of the closure")
        };
        nids.push(*id);
        nlangs.push(l);

        todo.extend(l.children());
    }
    (nids, nlangs)
}

pub(crate) fn rebuild_recexpr(ids: &[Id], lang: &[&Lang]) -> RecExpr<Lang> {
    lang.iter()
        .rev()
        .map(|l| {
            let head = l.head.clone();
            let args = l.args.iter().map(|cid| {
                let i = ids.iter().rev().position(|x| cid == x).unwrap();
                Id::new_const(i.try_into().unwrap())
            });
            Lang::new(head, args)
        })
        .collect()
}

pub fn generic<N: Analysis<Lang>, F: FnMut(&Lang) -> bool>(
    egraph: &EGraph<Lang, N>,
    filter: F,
    id: Id,
) -> Result<RecExpr<Lang>, Id> {
    let mut id_buffer = Vec::new();
    let mut recexpr_buffer = Vec::new();

    inner_generic(egraph, filter, id, &mut id_buffer, &mut recexpr_buffer)?;

    // all the ids referenced in `recexpr_buffer` are in `id_buffer`
    debug_assert!(
        recexpr_buffer
            .iter()
            .flat_map(|x| x.as_ref().into_iter())
            .flat_map(|l| l.children())
            .all(|c| id_buffer.contains(c))
    );

    // let mut reachable = vec![false; recexpr_buffer.len()];
    // filter_unreachable(&id_buffer, &recexpr_buffer, &mut reachable);
    let (ids, langs) = topo_sort(&id_buffer, &recexpr_buffer);
    let recexpr = rebuild_recexpr(&ids, &langs);
    debug_assert!(recexpr.is_dag());
    Ok(recexpr)
}

/// Does the same thing as [EGraph::id_to_expr] but make sure all function used
/// are not restricted to only prolog
///
/// ## panic
///  If it's not possible
pub fn no_prolog<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> Result<RecExpr<Lang>, Id> {
    generic(egraph, |f| !f.head.is_prolog_only(), id)
}
