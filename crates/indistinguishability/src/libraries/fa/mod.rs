use std::borrow::Cow;
use std::cell::RefCell;
use std::fmt::{Debug, Display};
use std::rc::Rc;

use egg::{Analysis, EClass, EGraph, Id, Pattern, SearchMatches, Searcher, Subst};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain, izip};
use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::{SmallVec, smallvec};
use static_init::dynamic;
use utils::{dynamic_iter, econtinue_if, econtinue_let, ereturn_if, ereturn_let};

use crate::libraries::utils::lambda_subst::lambda_subst;
use crate::libraries::utils::{Side, find_available_id};
use crate::problem::{PAnalysis, PRule, RcRule};
use crate::terms::list::{snoc_egraph, try_get_egraph};
use crate::terms::{
    AND, CONS_FA_BITSTRING, CONS_FA_BOOL, EMPTY, EQUIV, EXISTS, FIND_SUCH_THAT, FROM_BOOL,
    Function, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MITE, NIL_FA, NONCE,
    PRED, Sort, TUPLE,
};
use crate::{CVProgram, Lang, Problem, rexp};

declare_trace!($"fa");
decl_vars!(const; HD:Bitstring, TL:Bitstring, U, V, T, P, M:Bitstring);

decl_vars!(pub const; A, B);

#[dynamic]
pub static PATTERN_FA: Pattern<Lang> = Pattern::from(&rexp!((EQUIV #U #V #A #B)));

/// A rule for handling forall quantifiers.
pub struct FaRule;

pub fn mk_prolog_rules(_: &Problem) -> impl Iterator<Item = RcRule> {
    [FaRule.into_mrc()].into_iter()
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct FaElem {
    pub a: Id,
    pub b: Id,
    sort: LSort,
    splittable: bool,
}

struct PrintFa<'a, N: Analysis<Lang>> {
    egraph: &'a EGraph<Lang, N>,
    fa: &'a FaElem,
}

impl FaElem {
    pub fn get(&self, side: Side) -> Id {
        match side {
            Side::Left => self.a,
            Side::Right => self.b,
        }
    }

    pub fn set(&self, side: Side, x: Id) -> Self {
        match side {
            Side::Left => Self { a: x, ..*self },
            Side::Right => Self { b: x, ..*self },
        }
    }

    pub fn display<'a, N: Analysis<Lang>>(
        &'a self,
        egraph: &'a EGraph<Lang, N>,
    ) -> impl Display + use<'a, N> {
        PrintFa { egraph, fa: self }
    }
}

impl<'a, N: Analysis<Lang>> Display for PrintFa<'a, N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "FaElem {{\n\ta:'{}'\n\tb:'{}'\n,.. }}",
            self.egraph.id_to_expr(self.fa.a).pretty(100),
            self.egraph.id_to_expr(self.fa.b).pretty(100)
        )
    }
}

/// Checks if the function can be applied for the given function symbol.
fn can_apply_fa(f: &Function) -> bool {
    (f != &NONCE) && (f != &AND) && (f.is_part_of_F() || (f == &EXISTS) || (f == &FIND_SUCH_THAT))
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

        let fal2 = FaList2::new(*a, *b);
        let res = fal2.step_all(egraph);
        let iter = res
            .into_iter()
            .map(|l| l.iter().unique().cloned().collect())
            .unique()
            .map(|l| (subst, l));
        candidates.extend(iter);

        // let nc = extract_list(egraph, *a, *b);
        // let nc = nc.map(|fa| fa.iter().unique().cloned().collect());
        // candidates.extend(nc.map(|fa| (subst, fa)));

        // let ll_a = extract_list(egraph, *a);
        // let ll_b = extract_list(egraph, *b);
        // for list_a in &ll_a {
        //     tr!(
        //         "list_a: [\n\t{}\n]",
        //         list_a
        //             .iter()
        //             .map(|(is, s)| format!("{s:?}: {}", egraph.id_to_expr(*is).pretty(100)))
        //             .join(",\n\t")
        //     );
        //     for list_b in &ll_b {
        //         tr!("list_b: {list_b:?}");
        //         if list_a.len() != list_b.len() {
        //             continue 'out;
        //         }

        //         if let Some(list) = izip!(list_a, list_b)
        //             .map(|(&(a, sa), &(b, sb))| (sa == sb).then_some(FaElem { a, b, sort: sa }))
        //             .collect()
        //         {
        //             tr!("fa: add to candidates");
        //             candidates.push((subst, list))
        //         }
        //     }
        // }
    }
    assert!(substs.substs.is_empty() || !candidates.is_empty());
    candidates
}

#[dynamic]
static PATTERN_LIST_M: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA_BITSTRING #HD #TL)));
#[dynamic]
static PATTERN_LIST_B: Pattern<Lang> = Pattern::from(&rexp!((CONS_FA_BOOL #HD #TL)));
#[dynamic]
static PATTERN_LIST_TUPLE: Pattern<Lang> = Pattern::from(&rexp!((TUPLE #HD #TL)));

fn search_for_pattern_list<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    id: Id,
) -> Option<(Subst, LSort)> {
    if let Some(mut matches) = PATTERN_LIST_B.search_eclass(egraph, id) {
        return Some((matches.substs.pop().unwrap(), LSort::Bool));
    }

    if let Some(mut matches) = PATTERN_LIST_TUPLE.search_eclass(egraph, id) {
        return Some((matches.substs.pop().unwrap(), LSort::Bitstring));
    }

    if let Some(mut matches) = PATTERN_LIST_M.search_eclass(egraph, id) {
        return Some((matches.substs.pop().unwrap(), LSort::Bitstring));
    }

    None
}

#[dynamic]
static PATTERN_SKIP_BOILER_PLATE: Pattern<Lang> = Pattern::from(&rexp!((TUPLE
  (TUPLE (FROM_BOOL (MACRO_EXEC #T #P)) (MITE (MACRO_EXEC #T #P) #M EMPTY))
  (MACRO_FRAME (PRED #T) #P)
)));

#[dynamic]
static PATTERN_NIL: Pattern<Lang> = Pattern::from(&rexp!(NIL_FA));

#[derive(Debug, Default, PartialEq, Eq)]
struct FaList(Rc<RefCell<rpds::List<FaElem>>>);

#[derive(Debug, Clone)]
struct TodoListItem {
    ida: Id,
    idb: Id,
    /// current sort of the ids
    sort: LSort,
    /// nodes extracted
    list: FaList,
    /// nodes visited during the dfs
    visited: rpds::HashTrieSet<(Id, Id)>,
}

impl TodoListItem {
    pub fn new(ida: Id, idb: Id) -> Self {
        Self {
            ida,
            idb,
            sort: LSort::Bitstring,
            list: Default::default(),
            visited: Default::default(),
        }
    }
}

impl FaList {
    pub fn push(&self, elem: FaElem) {
        let x = self.0.borrow().push_front(elem);
        *self.0.borrow_mut() = x;
    }

    pub fn into_inner(self) -> rpds::List<FaElem> {
        // match Rc::try_unwrap(self.0) {
        //     Ok(x) => x.into_inner(),
        //     Err(x) => panic!("still got {:} references", Rc::strong_count(&x))
        // }
        self.0.borrow().clone()
    }
}

impl Clone for FaList {
    fn clone(&self) -> Self {
        // Self(self.0.clone())
        Self(Rc::new(RefCell::new(self.0.borrow().clone())))
    }
}

/// just to quickly make sure the sorts make sense
#[inline]
fn debug_check_sort<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id, sort: LSort) {
    debug_assert!(
        egraph[id]
            .nodes
            .iter()
            .map(|l| l.head.signature.output)
            .filter(|s| s != &Sort::Any)
            .chain(::std::iter::once(sort.as_sort()))
            .all_equal(),
        "mistyping [{}]",
        egraph[id].nodes.iter().join(", ")
    );
}

fn split<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    fa @ FaElem { a: ida, b: idb, .. }: FaElem,
) -> Vec<SmallVec<[FaElem; 3]>> {
    assert!(fa.splittable);

    tr!("spliting {}", fa.display(egraph));

    if let Some(ma) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, ida)
        && let Some(mb) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, idb)
    {
        let iter = ma
            .substs
            .iter()
            .cartesian_product(mb.substs.iter())
            .map(|(sa, sb)| {
                let ntodos_a = extra_shortcut_pattern(egraph, sa);
                let ntodos_b = extra_shortcut_pattern(egraph, sb);
                izip!(ntodos_a, ntodos_b)
                    .map(|((ida, sorta), (idb, sortb))| {
                        debug_assert_eq!(sorta, sortb);
                        FaElem {
                            a: ida,
                            b: idb,
                            sort: sorta,
                            splittable: true,
                        }
                    })
                    .collect()
            });
        return iter.collect();
    }

    if is_constant(egraph, ida) && is_constant(egraph, idb) {
        tr!("drop constant:\n\t{}", fa.display(egraph));
        // return Some(res);
        return Vec::new();
    }

    let mut res = Vec::new();

    let iter = egraph[ida]
        .nodes
        .iter()
        .cartesian_product(egraph[idb].nodes.iter());

    let n = res.len();
    // for Lang { head, args } in &egraph[id].nodes {
    for (
        Lang { head, args: argsa },
        Lang {
            head: hb,
            args: argsb,
        },
    ) in iter
    {
        if (head.is_prolog_only() || hb.is_prolog_only()) && !head.is_quantifier() {
            // we skip, there *will* be another one
            continue;
        } else if head == hb && (head == &TUPLE || head == &CONS_FA_BITSTRING) {
            res.push(smallvec![
                FaElem {
                    a: argsa[0],
                    b: argsb[0],
                    sort: LSort::Bitstring,
                    splittable: true
                },
                FaElem {
                    a: argsa[1],
                    b: argsb[1],
                    sort: LSort::Bitstring,
                    splittable: true
                },
            ])
        } else if head == hb && (head == &CONS_FA_BOOL) {
            res.push(smallvec![
                FaElem {
                    a: argsa[0],
                    b: argsb[0],
                    sort: LSort::Bool,
                    splittable: true
                },
                FaElem {
                    a: argsa[1],
                    b: argsb[1],
                    sort: LSort::Bitstring,
                    splittable: true
                },
            ]);
        } else {
            res.push(smallvec![FaElem {
                splittable: false,
                ..fa
            }]);
        };
    }
    assert!(
        res.len() > n,
        "needs to go through a non prolog-only branch"
    );
    res
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct FaList2 {
    todo: Vec<FaElem>,
    done: Vec<FaElem>,
}

impl FaList2 {
    pub fn new(ida: Id, idb: Id) -> Self {
        Self {
            todo: vec![FaElem {
                a: ida,
                b: idb,
                sort: LSort::Bitstring,
                splittable: true,
            }],
            done: Default::default(),
        }
    }

    pub fn step_one<N: Analysis<Lang>>(
        self,
        egraph: &EGraph<Lang, N>,
    ) -> impl Iterator<Item = Self> {
        dynamic_iter!(Iter; A:A, B:B);
        let FaList2 { mut todo, done } = self;

        match todo.pop() {
            Some(fa) => {
                let splitted = split(egraph, fa);
                if splitted.is_empty() {
                    Iter::A(::std::iter::once(FaList2 { todo, done }))
                } else {
                    Iter::B(splitted.into_iter().map(move |x| {
                        // x.into_iter().pa(|x| x.splittable);
                        let mut done = done.clone();
                        let mut todo = todo.clone();
                        for fa in x {
                            if fa.splittable {
                                tr!("ntodo {}", fa.display(egraph));
                                todo.push(fa);
                            } else {
                                tr!("done {}", fa.display(egraph));
                                done.push(fa);
                            }
                        }
                        tr!(
                            "todo = [{}]",
                            todo.iter().map(|x| x.display(egraph)).join(",\n")
                        );
                        FaList2 { todo, done }
                    }))
                }
            }
            _ => panic!("nothing to be done"),
        }
    }

    pub fn is_done(&self) -> bool {
        self.todo.is_empty()
    }

    pub fn step_all<N: Analysis<Lang>>(self, egraph: &EGraph<Lang, N>) -> Vec<Vec<FaElem>> {
        let mut todo = vec![self];
        let mut done = Vec::new();

        while let Some(e) = todo.pop() {
            tr!(
                "todo.todo = [{}]",
                e.todo.iter().map(|x| x.display(egraph)).join(",\n")
            );
            if e.is_done() {
                done.push(e.done)
            } else {
                todo.extend(e.step_one(egraph));
            }
            tr!("{:}", todo.len());
        }
        done
    }
}

// fn extract_list_inner<N: Analysis<Lang>>(
//     egraph: &EGraph<Lang, N>,
//     // to append things to do
//     todos: &mut Vec<TodoListItem>,
//     // current item under consideration
//     TodoListItem {
//         ida,
//         idb,
//         sort,
//         list,
//         mut visited,
//     }: TodoListItem,
// ) -> Option<FaList> {
//     debug_check_sort(egraph, ida, sort);
//     debug_check_sort(egraph, idb, sort);

//     if visited.contains(&(ida, idb)) {
//         list.push(FaElem {
//             a: ida,
//             b: idb,
//             sort,
//         });
//         return Some(list);
//     } else {
//         visited = visited.insert((ida, idb))
//     }

//     if let Some(ma) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, ida)
//         && let Some(mb) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, idb)
//     {
//         for (sa, sb) in ma.substs.iter().cartesian_product(mb.substs.iter()) {
//             let ntodos_a = extra_shortcut_pattern(egraph, sa);
//             let ntodos_b = extra_shortcut_pattern(egraph, sb);
//             let ntodos = izip!(ntodos_a, ntodos_b).map(|((ida, sorta), (idb, sortb))| {
//                 debug_assert_eq!(sorta, sortb);
//                 TodoListItem {
//                     ida,
//                     idb,
//                     sort: sorta,
//                     list: list.clone(),
//                     visited: visited.clone(),
//                 }
//             });
//             todos.extend(ntodos);
//         }
//         None
//     } else if is_constant(egraph, ida) || is_constant(egraph, idb) {
//         tr!("drop constant:\n\t{}", egraph.id_to_expr(ida).pretty(100));
//         tr!("drop constant:\n\t{}", egraph.id_to_expr(idb).pretty(100));
//         // return Some(res);
//         list.push(FaElem {
//             a: ida,
//             b: idb,
//             sort,
//         });
//         Some(list)
//     } else {
//         let iter = egraph[ida]
//             .nodes
//             .iter()
//             .cartesian_product(egraph[idb].nodes.iter());
//         // for Lang { head, args } in &egraph[id].nodes {
//         for (
//             Lang { head, args: argsa },
//             Lang {
//                 head: hb,
//                 args: argsb,
//             },
//         ) in iter
//         {
//             let ntodos = if !head.is_quantifier() && (head.is_prolog_only() || hb.is_prolog_only())
//             {
//                 // we skip, there *will* be another one
//                 continue;
//             } else if head == hb && (head == &TUPLE || head == &CONS_FA_BITSTRING) {
//                 [
//                     (argsa[0], argsb[0], LSort::Bitstring),
//                     (argsa[1], argsb[1], LSort::Bitstring),
//                 ]
//             } else if head == hb && (head == &CONS_FA_BOOL) {
//                 [
//                     (argsa[0], argsa[0], LSort::Bool),
//                     (argsa[1], argsb[1], LSort::Bitstring),
//                 ]
//             } else {
//                 // Shouldn't be possible to get to the other non-prolog-only branch
//                 list.push(FaElem {
//                     a: ida,
//                     b: idb,
//                     sort,
//                 });
//                 return Some(list);
//             };
//             let ntodos = ntodos.into_iter().map(|(ida, idb, sort)| TodoListItem {
//                 ida,
//                 idb,
//                 sort,
//                 list: list.clone(),
//                 visited: visited.clone(),
//             });
//             todos.extend(ntodos);
//         }
//         None
//     }
// }

fn extra_shortcut_pattern<N: Analysis<Lang>>(
    egraph: &EGraph<Lang, N>,
    subts: &Subst,
) -> [(Id, LSort); 3] {
    let t = *subts.get(T.as_egg()).unwrap();
    let p = *subts.get(P.as_egg()).unwrap();
    let pred_t = egraph.lookup(PRED.app_id([t])).unwrap();
    let mframe = egraph.lookup(MACRO_FRAME.app_id([pred_t, p])).unwrap();
    let mmsg = *subts.get(M.as_egg()).unwrap();
    // egraph.lookup(MACRO_MSG.app_id([t, p])).unwrap();
    let mcond = egraph.lookup(MACRO_COND.app_id([t, p])).unwrap();
    [
        (mframe, LSort::Bitstring),
        (mmsg, LSort::Bitstring),
        (mcond, LSort::Bool),
    ]
}

// Extracts a list of ids from the egraph starting from the given id.
// pub fn extract_list<N: Analysis<Lang>>(
//     egraph: &EGraph<Lang, N>,
//     inita: Id,
//     initb: Id,
// ) -> impl Iterator<Item = rpds::List<FaElem>> {
//     let mut todos = vec![TodoListItem::new(inita, initb)];

//     let mut res = Vec::new();

//     while let Some(todo) = todos.pop() {
//         let nres = extract_list_inner(egraph, &mut todos, todo);
//         if let Some(r) = nres {
//             res.push(r);
//         }
//     }
//     res.into_iter().map(|x| x.into_inner()).unique()
// }

// Extracts a list of ids from the egraph starting from the given id.
// FIXME !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
// pub fn extract_list<N: Analysis<Lang>>(
//     egraph: &EGraph<Lang, N>,
//     init: Id,
// ) -> Vec<Vec<(Id, LSort)>> {
//     todo!("fixme");
//     // if egraph[init]
//     //     .nodes
//     //     .iter()
//     //     .all(|f| f.head != CONS_FA_BITSTRING && f.head != CONS_FA_BOOL)
//     // {
//     //     return Some(vec![(init, LSort::Bitstring)]);
//     // }

//     let mut visited = FxHashSet::default();
//     let mut res = Vec::new();
//     let mut todos = vec![vec![(init, LSort::Bitstring)]];
//     while let Some((next, sort)) = todo.pop()
//         && !visited.contains(&next)
//     {
//         visited.insert(next);
//         if let Some(matches) = PATTERN_SKIP_BOILER_PLATE.search_eclass(egraph, next) {
//             let mut ntodos = Vec::with_capacity(todos.len() * matches.substs.len());
//             for todo in todos {
//                 for subts in &matches.substs {
//                     ntodos.push(todo.clone());
//                     let mut todo = ntodos.last().unwrap();

//                     let t = *subts.get(T.as_egg()).unwrap();
//                     let p = *subts.get(P.as_egg()).unwrap();
//                     let pred_t = egraph.lookup(PRED.app_id([t])).unwrap();
//                     let mframe = egraph.lookup(MACRO_FRAME.app_id([pred_t, p])).unwrap();
//                     let mmsg = *subts.get(M.as_egg()).unwrap(); // egraph.lookup(MACRO_MSG.app_id([t, p])).unwrap();
//                     let mcond = egraph.lookup(MACRO_COND.app_id([t, p])).unwrap();
//                     todo.extend_from_slice(&[
//                         (mframe, LSort::Bitstring),
//                         (mmsg, LSort::Bitstring),
//                         (mcond, LSort::Bool),
//                     ]);
//                 }
//             }
//             todos = ntodos;
//             // let subts = &matches.substs[0];
//         } else if let Some((subst, sort)) = search_for_pattern_list(egraph, next) {
//             for todo in &mut todos {
//                 todo.push((*subst.get(HD.as_egg()).unwrap(), sort));
//                 todo.push((*subst.get(TL.as_egg()).unwrap(), sort));
//                 // res.push((*subst.get(HD.as_egg()).unwrap(), sort));
//                 // next = *subst.get(TL.as_egg()).unwrap();
//                 // } else if PATTERN_NIL.search_eclass(egraph, next).is_some() {
//             }
//         } else if is_constant(egraph, next) {
//             tr!("drop constant:\n\t{}", egraph.id_to_expr(next).pretty(100));
//             // return Some(res);
//             continue;
//         } else {
//             debug_assert!(
//                 egraph[next]
//                     .nodes
//                     .iter()
//                     .map(|l| l.head.signature.output)
//                     .filter(|s| s != &Sort::Any)
//                     .chain(::std::iter::once(sort.as_sort()))
//                     .all_equal(),
//                 "mistyping [{}]",
//                 egraph[next].nodes.iter().join(", ")
//             );
//             res.push((next, sort));
//         }
//     }
//     res
// }

fn is_constant<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> bool {
    egraph[id]
        .nodes
        .iter()
        .filter(|f| f.head.is_part_of_F())
        .any(|Lang { head, .. }| head.args_sorts().all(|s| !s.is_base() && s != Sort::Nonce))
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum LSort {
    Bool,
    Bitstring,
}

impl TryFrom<Sort> for LSort {
    type Error = ();

    fn try_from(value: Sort) -> Result<Self, Self::Error> {
        match value {
            Sort::Bool => Ok(LSort::Bool),
            Sort::Bitstring => Ok(LSort::Bitstring),
            _ => Err(()),
        }
    }
}

impl LSort {
    pub fn to_cons_fn(self) -> &'static Function {
        match self {
            Self::Bitstring => &CONS_FA_BITSTRING,
            Self::Bool => &CONS_FA_BOOL,
        }
    }

    pub fn as_sort(&self) -> Sort {
        match self {
            Self::Bitstring => Sort::Bitstring,
            Self::Bool => Sort::Bool,
        }
    }
}
