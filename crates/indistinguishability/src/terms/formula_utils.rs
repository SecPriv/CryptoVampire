//! This module mostly exists for the macro [rexp] to pull it's functions from.
//! It also contains other miscelenious functions

use crate::{
    Lang, LangVar,
    terms::{Function, Sort},
};
use egg::{Analysis, EGraph, ENodeOrVar, Id, Language, PatternAst, RecExpr, Var, VarExposed};
use itertools::{EitherOrBoth, Itertools, izip};
use log::error;
use logic_formula::{Destructed, Formula, HeadSk, egg::SimplLang};
use std::{borrow::Cow, collections::VecDeque};
use utils::{ebreak_if, econtinue_if, econtinue_let, ereturn_if, implvec};

declare_trace!($"formula_utils");

/// magic ✨
#[macro_export]
macro_rules! rexp {
    ($($t:tt)*) => {
        ::cryptovampire_macros::recexpr!($crate::terms::formula_utils; $($t)*)
    };
}

/// for [rexp]
pub static TRUE: Function = super::TRUE.const_clone().unwrap();
/// for [rexp]
pub static FALSE: Function = super::TRUE.const_clone().unwrap();
/// for [rexp]
pub static AND: Function = super::AND.const_clone().unwrap();
/// for [rexp]
pub static OR: Function = super::OR.const_clone().unwrap();
/// for [rexp]
pub static NOT: Function = super::NOT.const_clone().unwrap();
/// for [rexp]
pub static EQ: Function = super::EQ.const_clone().unwrap();
/// for [rexp]
pub static IMPLIES: Function = super::IMPLIES.const_clone().unwrap();

/// for [rexp]
pub const fn mk_var(i: u32) -> LangVar {
    egg::ENodeOrVar::Var(Var::from_u32(i))
}

/// for [rexp]
pub fn mk_app(head: &Function, args: implvec!(u32)) -> LangVar {
    egg::ENodeOrVar::ENode(SimplLang::new(
        head.clone(),
        args.into_iter().map(Id::new_const),
    ))
}

/// Turn an iterator of [LangVar] into a [Cow]ed array
pub fn convert_to_cow(c: implvec!(LangVar)) -> Cow<'static, [LangVar]> {
    c.into_iter().collect()
}

/// Turn an iterator of [LangVar] in a [RecExpr] withtout variable. Returns the
/// first encountered variable as an [Err].
pub fn convert_to_ground_rexp(c: implvec!(LangVar)) -> Result<RecExpr<crate::Lang>, egg::Var> {
    let tmp: PatternAst<crate::Lang> = c.into_iter().collect();
    tmp.try_into()
}

/// **!!! DON'T USE DIRECTLY !!!**
///
/// alias for [rexp]
pub type RexpLang = LangVar;

pub fn get_sort<'a, F>(f: &'a F) -> Option<Sort>
where
    &'a F: Formula,
    F: ?Sized,
    <&'a F as Formula>::Fun: AsRef<Function>,
{
    match f.head() {
        HeadSk::Var(_) => None,
        HeadSk::Fun(f) => Some(f.as_ref().signature.output),
        HeadSk::Quant(_) => Some(Sort::Bool),
    }
}

pub fn type_check<'a, F>(f: &'a F) -> bool
where
    &'a F: Formula,
    F: ?Sized,
    <&'a F as Formula>::Fun: AsRef<Function>,
{
    let Destructed { head, args } = f.destruct();
    match head {
        HeadSk::Var(_) => true,
        HeadSk::Fun(fun) => {
            Itertools::zip_longest(fun.as_ref().signature.inputs_iter(), args).all(|x| match x {
                EitherOrBoth::Both(asort, arg) => {
                    type_check(arg) && get_sort(arg).map(|x| x == asort).unwrap_or(true)
                }
                _ => false,
            })
        }
        HeadSk::Quant(_) => izip!(::std::iter::repeat(Sort::Bool), args).all(|(asort, arg)| {
            type_check(arg) && get_sort(arg).map(|x| x == asort).unwrap_or(true)
        }),
    }
}

pub fn offsets_vars<L>(amount: u32, f: &mut [ENodeOrVar<L>]) {
    for e in f {
        if let ENodeOrVar::Var(v) = e
            && let VarExposed::Num(i) = v.expose()
        {
            *v = (i + amount).into()
        }
    }
}
pub fn offsets_owned<L>(amount: u32, f: implvec!(ENodeOrVar<L>)) -> PatternAst<L> {
    let mut f: PatternAst<L> = f.into_iter().collect();
    offsets_vars(amount, &mut f);
    f
}

pub(crate) fn pull_from_egraph_inner<'a, N: Analysis<Lang>>(
    egraph: &'a EGraph<Lang, N>,
    id: Id,
    id_buffer: &mut Vec<Id>,
    recexpr_buffer: &mut Vec<Option<&'a Lang>>,
) -> Option<()> {
    debug_assert!(!id_buffer.contains(&id));
    debug_assert_eq!(id_buffer.len(), recexpr_buffer.len());
    let eclass = &egraph[id];
    let len = recexpr_buffer.len();
    id_buffer.push(id);
    recexpr_buffer.push(None);

    'enodes: for e in eclass.iter().filter(|x| !x.head.is_prolog_only()) {
        'children: for cid in Language::children(e) {
            if let Some(i) = id_buffer.iter().position(|id| id == cid) {
                if recexpr_buffer[i].is_some() {
                    continue 'children;
                } else {
                    continue 'enodes;
                }
            }

            econtinue_if!('enodes, pull_from_egraph_inner(egraph, *cid, id_buffer, recexpr_buffer).is_none());

            if cfg!(debug_assertions) {
                debug_assert_eq!(id_buffer.len(), recexpr_buffer.len());
                let (i, _) = id_buffer.iter().find_position(|x| x == &cid).unwrap();
                assert!(recexpr_buffer[i].is_some())
            }
        }

        // if we reach that point, we can save the result and exit
        recexpr_buffer[len] = Some(e);
        return Some(());
    }

    // faillure case
    if cfg!(debug_assertions) {
        let e = egraph.id_to_expr(id);
        error!(
            "{e:} cannot be turned into a non recursive formula without using \"prolog\"-specific functions"
        )
    }
    None
}

fn topo_sort<'a>(ids: &[Id], langs: &[Option<&'a Lang>]) -> (Vec<Id>, Vec<&'a Lang>) {
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

fn rebuild_recexpr(ids: &[Id], lang: &[&Lang]) -> RecExpr<Lang> {
    lang.iter()
        .rev()
        .map(|l| {
            let head = l.head.clone();
            let args = l
                .args
                .iter()
                .map(|cid| {
                    let i = ids.iter().rev().position(|x| cid == x).unwrap();
                    Id::new_const(i.try_into().unwrap())
                });
            Lang::new(head, args)
        })
        .collect()
}

/// Does the same thing as [EGraph::id_to_expr] but make sure all function used
/// are not restricted to only prolog
///
/// ## panic
///  If it's not possible
pub fn pull_from_egraph<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    id: Id,
) -> Option<RecExpr<Lang>> {
    let mut id_buffer = Vec::new();
    let mut recexpr_buffer = Vec::new();

    pull_from_egraph_inner(egraph, id, &mut id_buffer, &mut recexpr_buffer)?;

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
    Some(recexpr)
}

#[cfg(test)]
mod test {
    use crate::terms::{MITE, NONCE, PROJ_1, TUPLE, formula_utils::type_check};

    #[test]
    fn type_check_true() {
        let x =
            rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE #1 (NONCE #0))))).to_vec();
        assert!(type_check(x.as_slice()))
    }

    #[test]
    fn type_check_wrong_length() {
        let x = rexp!((MITE (and true true false) (NONCE #0) (PROJ_1 (TUPLE (NONCE #0))))).to_vec();
        assert!(!type_check(x.as_slice()))
    }

    #[test]
    fn type_check_wrong_sort() {
        let x = rexp!((MITE (and true true false) (and ) (PROJ_1 (TUPLE (NONCE #0))))).to_vec();
        assert!(!type_check(x.as_slice()))
    }
}
