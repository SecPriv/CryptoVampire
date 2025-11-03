use std::borrow::Cow;
use std::fmt::Debug;

use egg::{Analysis, EClass, EGraph, Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain, izip};
use log::trace;
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use static_init::dynamic;
use utils::{econtinue_if, econtinue_let, ereturn_if, ereturn_let};

use crate::problem::{PAnalysis, PRule, RcRule};
use crate::rules::utils::lambda_subst::lambda_subst;
use crate::terms::list::{snoc_egraph, try_get_egraph};
use crate::terms::{CONS_FA, EQUIV, EXISTS, FIND_SUCH_THAT, Function, NIL_FA, Sort};
use crate::{Lang, Problem, rexp};

declare_trace!($"fa");
decl_vars!(const; HD:Bitstring, TL:Bitstring, U, V, A, B);

#[dynamic]
static PATTERN_LIST: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA #HD #TL)));
#[dynamic]
static PATTERN_FA: Pattern<Lang> = Pattern::from(&rexp!((EQUIV #U #V #A #B)));

/// Creates the rules for the `fa` module.
pub fn mk_rules(_: &Problem) -> impl Iterator<Item = RcRule> + use<'_> {
    [FaRule.into_mrc()].into_iter()
}

/// Checks if the function can be applied for the given function symbol.
fn can_apply_fa(f: &Function) -> bool {
    f.is_part_of_F() || (f == &EXISTS) || (f == &FIND_SUCH_THAT)
}

/// A rule for handling forall quantifiers.
pub struct FaRule;

impl<'a> Rule<Lang, PAnalysis<'a>> for FaRule {
    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fa")
    }

    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        // Get the substitutions that match the pattern for the goal.
        ereturn_let!(let Some(substs) = PATTERN_FA.search_eclass(prgm.egraph(), goal), Dependancy::impossible());
        tr!("into fa-axiom");

        // find suitable substitutions and arguments
        // we need to collect now, because the egraph will get dirty later
        let mut candidates = Vec::with_capacity(substs.substs.len());
        {
            // immutable `egraph`
            let egraph = prgm.egraph();
            for subst in &substs.substs {
                econtinue_let!(let Some(a) = subst.get(A.as_egg()));
                econtinue_let!(let Some(b) = subst.get(B.as_egg()));
                tr!(
                    "fa-axiom found potential instance:\n\t{}\n\t{}",
                    egraph.id_to_expr(*a).pretty(80),
                    egraph.id_to_expr(*b).pretty(80)
                );

                // Extract lists for 'a' and 'b', continue if not a list or the lengths don't match
                econtinue_let!(let Some(list_a) = extract_list(egraph, *a));
                tr!("list_a: {list_a:?}");
                econtinue_let!(let Some(list_b) = extract_list(egraph, *b));
                econtinue_if!(list_a.len() != list_b.len());

                candidates.push((subst, list_a, list_b))
            }
        };

        let mut results = Vec::new();
        {
            // mutable `egraph`
            let egraph = prgm.egraph_mut();
            for (subst, list_a, list_b) in candidates {
                // Collect sets of arguments for creating new expressions.
                let sets = collect_sets(egraph, &list_a, &list_b);
                // Create new expressions and add them to the egraph.
                results.extend(sets.into_iter().map(|args| {
                    let (ia_id, ib_id) = create_lists(egraph, &args);
                    let u = *subst.get(U.as_egg()).unwrap();
                    let v = *subst.get(V.as_egg()).unwrap();
                    egraph.add(EQUIV.app_id([u, v, ia_id, ib_id]))
                }))
            }
        }
        results.into_iter().map(::std::iter::once).collect()
    }
}

/// Extracts a list of ids from the egraph starting from the given id.
fn extract_list<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, init: Id) -> Option<Vec<Id>> {
    ereturn_if!(
        PATTERN_LIST.search_eclass(egraph, init).is_none(),
        Some(vec![init])
    );

    let mut visited = FxHashSet::default();
    let mut res = Vec::new();
    let mut next = init;
    while !visited.contains(&next) {
        if let Some(matches) = PATTERN_LIST.search_eclass(egraph, next) {
            visited.insert(next);
            let subst = &matches.substs[0];
            res.push(*subst.get(HD.as_egg()).unwrap());
            next = *subst.get(TL.as_egg()).unwrap();
        } else if egraph[next].leaves().any(|n| n.head == NIL_FA) {
            return Some(res);
        } else {
            break;
        }
    }
    None
}

/// Collects sets of arguments for creating new expressions.
fn collect_sets<'a>(
    egraph: &mut EGraph<Lang, PAnalysis<'a>>,
    list_a: &[Id],
    list_b: &[Id],
) -> Vec<FxHashSet<(Id, Id)>> {
    let mut sets = Vec::new();
    // Iterate over pairs of elements from list_a and list_b.
    for (i, (ta, tb)) in izip!(list_a, list_b).enumerate() {
        let ea = &egraph[*ta];
        let eb = &egraph[*tb];
        // Find common heads and collect arguments.
        for (f, a_args, b_args) in find_commun_head(ea, eb).collect_vec() {
            // Collect pairs of arguments.
            let args = if f.is_quantifier() {
                mk_new_list(i, list_a, list_b, &f, &a_args, &b_args, |f, la, lb| {
                    q_transform(egraph, f, la, lb)
                })
            } else {
                mk_new_list(i, list_a, list_b, &f, &a_args, &b_args, f_transform)
            };

            econtinue_let!(let Some(args) = args);
            sets.push(args);
        }
    }
    sets
}

fn mk_new_list<'a, F, I>(
    i: usize,
    old_args_a: &[Id],
    old_args_b: &[Id],
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
    transfom: F,
) -> Option<FxHashSet<(Id, Id)>>
where
    F: FnOnce(&'a Function, &'a [Id], &'a [Id]) -> Option<I>,
    I: IntoIterator<Item = (Id, Id)> + 'a,
{
    let old = izip!(old_args_a, old_args_b)
        .enumerate()
        .filter_map(|(j, (&a, &b))| (i != j).then_some((a, b)));
    let new = transfom(f, n_args_a, n_args_b)?;
    Some(chain!(old, new).collect())
}

fn fa_must_keep_sort(s: Sort) -> bool {
    use Sort::*;
    matches!(s, Bitstring | Nonce | Bool)
}

/// transformation for regular functions
fn f_transform<'a>(
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
) -> Option<impl IntoIterator<Item = (Id, Id)> + use<'a>> {
    Some(
        izip!(f.signature.inputs_iter(), n_args_a, n_args_b)
            .filter_map(|(s, &a, &b)| fa_must_keep_sort(s).then_some((a, b))),
    )
}

/// transformation for quantifiers
fn q_transform<'e, 'a>(
    egraph: &'a mut EGraph<Lang, PAnalysis<'e>>,
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
) -> Option<impl IntoIterator<Item = (Id, Id)> + use<'a, 'e>> {
    assert!(f.is_egg_binder());
    tr!("here");

    let mut args = izip!(n_args_a.iter().copied(), n_args_b.iter().copied());

    let (s, tlsa, na, tlsb, nb) = {
        // checks sorts
        let (sa, sb) = args.next()?;
        let (sa, tlsa) = snoc_egraph(egraph, sa).unwrap()?;
        let (sb, tlsb) = snoc_egraph(egraph, sb).unwrap()?;
        ereturn_if!(sa != sb || !matches!(sa, Sort::Index | Sort::Time), None);
        let na = try_get_egraph(egraph, tlsa)?.len();
        let nb = try_get_egraph(egraph, tlsb)?.len();
        (sa, tlsa, na, tlsb, nb)
    };

    let new_var = egraph
        .analysis
        .pbl_mut()
        .declare_function()
        .output(s)
        .fresh_name("idx")
        .call();
    let new_var = egraph.add(Lang::new(new_var, []));

    let mut reta = SmallVec::with_capacity(f.arity());
    let mut retb = SmallVec::with_capacity(f.arity());
    reta.push(tlsa);
    retb.push(tlsb);
    let mut map = FxHashMap::default();

    if f == &EXISTS {
        let (a, b) = args.next().unwrap();
        let [na, nb] = [(na, a), (nb, b)].map(|(n, id)| {
            map.clear();
            lambda_subst(egraph, &mut map, new_var, n, id).unwrap()
        });
        reta.push(na);
        retb.push(nb);
    } else if f == &FIND_SUCH_THAT {
        let (ac, bc) = args.next().unwrap();
        let (al, bl) = args.next().unwrap();
        let (ar, br) = args.next().unwrap();

        let [nac, nbc, nal, nbl] = [(na, ac), (nb, bc), (na, al), (nb, bl)].map(|(n, id)| {
            map.clear();
            lambda_subst(egraph, &mut map, new_var, n, id).unwrap()
        });
        tr!(
            "q_transform:from:\n\t{}\n\tto\n\t{}",
            egraph.id_to_expr(ac).pretty(80),
            egraph.id_to_expr(nac).pretty(80)
        );
        reta.extend_from_slice(&[nac, nal, ar]);
        retb.extend_from_slice(&[nbc, nbl, br]);
    } else {
        unreachable!("{f}")
    }

    let na = egraph.add(Lang {
        head: f.clone(),
        args: reta,
    });
    let nb = egraph.add(Lang {
        head: f.clone(),
        args: retb,
    });
    Some([(na, nb)])
}

/// Creates lists in the egraph from a set of argument pairs.
fn create_lists<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    args: &FxHashSet<(Id, Id)>,
) -> (Id, Id) {
    // Create lists for the first and second elements of the argument pairs.
    let ia = args.iter().map(|(x, _)| *x);
    let ib = args.iter().map(|(_, x)| *x);
    let ia_id = mk_list(egraph, ia);
    let ib_id = mk_list(egraph, ib);
    (ia_id, ib_id)
}

/// Creates a list in the egraph from a list of terms.
fn mk_list<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    terms: impl IntoIterator<Item = Id>,
) -> Id {
    let init = egraph.add(NIL_FA.app_id([]));
    terms
        .into_iter()
        .fold(init, |acc, t| egraph.add(CONS_FA.app_id([t, acc])))
}

/// Finds common heads between two eclasses.
fn find_commun_head<'a, D: Debug>(
    a: &'a EClass<Lang, D>,
    b: &'a EClass<Lang, D>,
) -> impl Iterator<Item = (Function, Vec<Id>, Vec<Id>)> {
    a.nodes
        .iter()
        .cartesian_product(b.nodes.iter())
        .filter(|(a, b)| (a.head == b.head) && can_apply_fa(&a.head))
        .map(|(a, b)| {
            (
                a.head.clone(),
                a.args.clone().into_vec(),
                b.args.clone().into_vec(),
            )
        })
}
