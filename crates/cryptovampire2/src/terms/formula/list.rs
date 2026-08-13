use egg::{Analysis, EGraph, Id};
use itertools::Itertools;
use logic_formula::{AsFormula, Destructed};
use utils::econtinue_let;

use crate::Lang;
use crate::terms::{CONS, Function, LAMBDA_O, LAMBDA_S, NIL, Sort};

fn inner<F>(f: F, sorts: &mut Vec<Sort>) -> Option<()>
where
    F: AsFormula,
    F::Fun: AsRef<Function>,
{
    let Destructed { head, args } = f.destruct();

    match head.as_fun() {
        Some(f) if f.as_ref() == &CONS => {
            let (hd, tl) = args.collect_tuple()?;
            let s = Sort::from_function(hd.destruct().head.as_fun()?.as_ref())?;
            sorts.push(s);
            inner(tl, sorts)
        }
        Some(f) if f.as_ref() == &NIL => Some(()),
        _ => None,
    }
}

pub fn snoc_egraph<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    f: Id,
) -> Result<Option<(Sort, Id)>, Id> {
    match egraph[f]
        .nodes
        .iter()
        .find(|f| f.head == NIL || f.head == CONS)
        .ok_or(f)?
    {
        Lang { head, .. } if head == &NIL => Ok(None),
        Lang { head, args } if head == &CONS => {
            let (&s, &rec) = args.iter().collect_tuple().ok_or(f)?;
            for h in egraph[s].nodes.iter().map(|x| &x.head) {
                econtinue_let!(let Some(s) = Sort::from_function(h));
                return Ok(Some((s, rec)));
            }
            Err(f)
        }
        _ => unreachable!(),
    }
}

fn inner_egraph<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    mut f: Id,
    sorts: &mut Vec<Sort>,
) -> Option<()> {
    while let Some((s, tl)) = snoc_egraph(egraph, f).ok()? {
        sorts.push(s);
        f = tl
    }
    Some(())
}

/// Attempts to extract a list of sorts from a formula.
///
/// This function walks through a formula that is expected to be a list
/// constructed using [CONS] and [NIL]. For each element in the list,
/// it attempts to extract the sort of the head of that element.
///
/// # Arguments
///
/// * `f` - A formula representing a list, where elements are constructed
///   with `CONS` and terminated by `NIL`.
///
/// # Returns
///
/// * `Some(Vec<Sort>)` - A vector of sorts extracted from the list.
/// * `None` - If the input formula does not match the expected structure
///   (e.g., it's not a proper list or an element has no associated sort).
pub fn try_get<F>(f: F) -> Option<Vec<Sort>>
where
    F: AsFormula,
    F::Fun: AsRef<Function>,
{
    let mut sorts = vec![];
    inner(f, &mut sorts)?;
    Some(sorts)
}

/// Same as [try_get] but from an egraph
pub fn try_get_egraph<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, f: Id) -> Option<Vec<Sort>> {
    let mut sorts = vec![];
    inner_egraph(egraph, f, &mut sorts)?;
    Some(sorts)
}

#[allow(dead_code)]
pub fn count_s<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, f: Id) -> Option<u32> {
    for n in egraph[f].iter() {
        if n.head == LAMBDA_O {
            return Some(0);
        } else if n.head == LAMBDA_S {
            return count_s(egraph, n.args[0]);
        }
    }
    None
}
