use std::borrow::Cow;
use std::fmt::Debug;

use egg::{Analysis, EClass, EGraph, Id, Pattern, SearchMatches, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain, izip};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use static_init::dynamic;
use utils::{dynamic_iter, econtinue_if, econtinue_let, ereturn_if, ereturn_let};

use crate::libraries::utils::find_available_id;
use crate::libraries::utils::lambda_subst::lambda_subst;
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::list::{snoc_egraph, try_get_egraph};
use crate::terms::{
    AND, EMPTY, EQUIV, EXISTS, FIND_SUCH_THAT, Function, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT,
    NIL_FA, NONCE, PRED, Sort,
};
use crate::{CVProgram, Lang, Problem, rexp};

declare_trace!($"fa");
decl_vars!(const; HD:Bitstring, TL:Bitstring, U, V, T, P, M:Bitstring);

decl_vars!(pub const; A, B);

use split::{is_constant, split};
mod split;

pub use fa_elem::{FaElem, LSort, split_all};
mod fa_elem;

#[dynamic]
pub static PATTERN_FA: Pattern<Lang> = Pattern::from(&rexp!((EQUIV #U #V #A #B)));

/// A rule for handling forall quantifiers.
pub struct FaRule;

pub fn mk_prolog_rules(_: &Problem) -> impl Iterator<Item = RcRule> {
    [FaRule.into_mrc()].into_iter()
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for FaRule {
    /// Returns the name of the rule.
    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fa")
    }

    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        // Get the substitutions that match the pattern for the goal.
        ereturn_let!(let Some(substs) = PATTERN_FA.search_eclass(prgm.egraph(), goal), Dependancy::impossible());
        tr!("into fa-axiom");
        // find suitable substitutions and arguments
        // we need to collect now, because the egraph will get dirty later
        let candidates = find_candidates(prgm, &substs);

        let mut results = Vec::new();

        {
            // mutable `egraph`
            let egraph = prgm.egraph_mut();
            for (subst, list) in candidates {
                // Collect sets of arguments for creating new expressions.
                let sets = collect_sets(egraph, &list);
                tr!("sets:\n{sets:#?}");
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

pub fn find_candidates<'a, 'pbl>(
    prgm: &mut CVProgram<'pbl>,
    substs: &'a SearchMatches<'_, Lang>,
) -> Vec<(&'a Subst, Vec<FaElem>)> {
    let mut candidates: Vec<(&Subst, Vec<FaElem>)> = Vec::new();
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
        // econtinue_let!(let list_a = extract_list(egraph, *a));

        let iter = split_all(*a, *b, egraph)
            .into_iter()
            .map(|l| l.iter().unique().cloned().collect())
            .unique()
            .map(|l| (subst, l));
        candidates.extend(iter);
    }
    assert!(substs.substs.is_empty() || !candidates.is_empty());
    candidates
}

/// Checks if the function can be applied for the given function symbol.
fn can_apply_fa(f: &Function) -> bool {
    (f != &NONCE) && (f != &AND) && (f.is_part_of_F() || (f == &EXISTS) || (f == &FIND_SUCH_THAT))
}

/// Collects sets of arguments for creating new expressions.
fn collect_sets<'a>(egraph: &mut EGraph<Lang, PAnalysis<'a>>, list: &[FaElem]) -> Vec<Vec<FaElem>> {
    let mut sets = vec![list.to_vec()];
    // Iterate over pairs of elements from list_a and list_b.
    for (i, FaElem { a, b, .. }) in list.iter().enumerate() {
        let ea = &egraph[*a];
        let eb = &egraph[*b];
        // Find common heads and collect arguments.
        for (f, a_args, b_args) in find_commun_head(ea, eb).collect_vec() {
            // Collect pairs of argumentsEQUIV.
            let args = if f.is_quantifier() {
                mk_new_list(i, list, &f, &a_args, &b_args, |f, la, lb| {
                    q_transform(egraph, list, f, la, lb)
                })
            } else {
                mk_new_list(i, list, &f, &a_args, &b_args, f_transform)
            };

            econtinue_let!(let Some(args) = args);
            let optimzed = optimize_set(egraph, args);

            econtinue_if!(optimzed.len() > egraph.analysis.pbl().config.fa_limit);
            sets.push(optimzed);
        }
    }
    sets
}

#[dynamic]
static PATTERN_FRAME: Pattern<Lang> = Pattern::from(&rexp!((MACRO_FRAME #T #P)));
#[dynamic]
static PATTERN_FRAME_PRED: Pattern<Lang> = Pattern::from(&rexp!((MACRO_FRAME (PRED #T)  #P)));
#[dynamic]
static PATTERN_EXEC: Pattern<Lang> = Pattern::from(&rexp!((MACRO_EXEC #T #P)));
#[dynamic]
static PATTERN_INPUT: Pattern<Lang> = Pattern::from(&rexp!((MACRO_INPUT #T #P)));
#[dynamic]
static PATTERN_EMPTY: Pattern<Lang> = Pattern::from(&rexp!(EMPTY));

/// gets rid of some obviously non-optimal elements
///
/// e.g., if `frame_p@t` is in the set then we can remove `exec_p@t`
pub fn optimize_set<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    s: FxHashSet<FaElem>,
) -> Vec<FaElem> {
    let mut ret = Vec::with_capacity(s.len());
    let patt_frame: &Pattern<_> = &PATTERN_FRAME;
    let patt_frame_pred: &Pattern<_> = &PATTERN_FRAME_PRED;

    let [frame, frame_pred]: [FxHashSet<_>; 2] = [patt_frame, patt_frame_pred].map(|patt| {
        s.iter()
            .flat_map(|FaElem { a, b, .. }| match_both_side(egraph, patt, *a, *b))
            .collect()
    });

    for e @ FaElem { a, b, .. } in s {
        econtinue_if!(match_both_side(egraph, &PATTERN_EXEC, a, b).any(|x| frame.contains(&x)));
        econtinue_if!(
            match_both_side(egraph, &PATTERN_INPUT, a, b).any(|x| frame_pred.contains(&x))
        );
        econtinue_if!(
            match_both_side(egraph, &PATTERN_EMPTY, a, b)
                .next()
                .is_some()
        );
        econtinue_if!(a == b && is_constant(egraph, a));

        ret.push(e);
    }
    ret
}

fn match_both_side<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    patt: &Pattern<Lang>,
    a: Id,
    b: Id,
) -> impl Iterator<Item = (Subst, Subst)> {
    dynamic_iter!(Miter; Empty:A, Many:B);
    let empty = Miter::Empty(::std::iter::empty());

    ereturn_let!(let Some(sa) = patt.search_eclass(egraph, a), empty);
    ereturn_let!(let Some(sb) = patt.search_eclass(egraph, b), empty);
    Miter::Many(Itertools::cartesian_product(
        sa.substs.into_iter(),
        sb.substs,
    ))
}

fn mk_new_list<'a, F, I>(
    i: usize,
    old_arg: &[FaElem],
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
    transfom: F,
) -> Option<FxHashSet<FaElem>>
where
    F: FnOnce(&'a Function, &'a [Id], &'a [Id]) -> Option<I>,
    I: IntoIterator<Item = FaElem> + 'a,
{
    let old = old_arg
        .iter()
        .enumerate()
        .filter_map(|(j, &e)| (i != j).then_some(e));
    let new = transfom(f, n_args_a, n_args_b)?;

    Some(chain!(old, new).collect())
}

/// transformation for regular functions
fn f_transform<'a>(
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
) -> Option<impl IntoIterator<Item = FaElem> + use<'a>> {
    Some(
        izip!(f.signature.inputs_iter(), n_args_a, n_args_b).filter_map(|(s, &a, &b)| {
            let sort = s.try_into().ok()?;
            Some(FaElem {
                a,
                b,
                sort,
                splittable: false,
            })
        }),
    )
}

/// transformation for quantifiers
fn q_transform<'e, 'a>(
    egraph: &'a mut EGraph<Lang, PAnalysis<'e>>,
    old: &[FaElem],
    f: &'a Function,
    n_args_a: &'a [Id],
    n_args_b: &'a [Id],
) -> Option<impl IntoIterator<Item = FaElem> + use<'a, 'e>> {
    assert!(f.is_egg_binder());
    tr!("here : {f}");

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

    let new_var = find_available_id(
        egraph,
        s,
        chain![
            old.iter()
                .flat_map(|FaElem { a, b, .. }| [a, b].into_iter()),
            n_args_a,
            n_args_b
        ]
        .copied(),
    );

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
    Some([FaElem {
        a: na,
        b: nb,
        sort: f.signature.output.try_into().unwrap(),
        splittable: false,
    }])
}

/// Creates lists in the egraph from a set of argument pairs.
pub fn create_lists<N: Analysis<Lang>>(egraph: &mut EGraph<Lang, N>, args: &[FaElem]) -> (Id, Id) {
    // Create lists for the first and second elements of the argument pairs.
    let ia = args.iter().map(|FaElem { a, sort, .. }| (*a, *sort));
    let ib = args.iter().map(|FaElem { b, sort, .. }| (*b, *sort));
    let ia_id = mk_list(egraph, ia);
    let ib_id = mk_list(egraph, ib);
    (ia_id, ib_id)
}

/// Creates a list in the egraph from a list of terms.
fn mk_list<N: Analysis<Lang>>(
    egraph: &mut EGraph<Lang, N>,
    terms: impl IntoIterator<Item = (Id, LSort)>,
) -> Id {
    let init = egraph.add(NIL_FA.app_id([]));
    terms.into_iter().fold(init, |acc, (t, s)| {
        egraph.add(s.to_cons_fn().app_id([t, acc]))
    })
}

/// Finds common heads between two eclasses.
fn find_commun_head<'a, D: Debug>(
    a: &'a EClass<Lang, D>,
    b: &'a EClass<Lang, D>,
) -> impl Iterator<Item = (Function, Vec<Id>, Vec<Id>)> {
    tr!("looking for commun head");
    a.nodes
        .iter()
        .cartesian_product(b.nodes.iter())
        .inspect(|(a, b)| tr!("trying to find commun head :{a}, {b}"))
        .filter(|(a, b)| (a.head == b.head) && can_apply_fa(&a.head))
        .map(|(a, b)| {
            (
                a.head.clone(),
                a.args.clone().into_vec(),
                b.args.clone().into_vec(),
            )
        })
}
