use std::{borrow::Cow, default, env::vars, fmt::Display};

use egg::*;
use itertools::{chain, izip, Itertools};
use rustc_hash::{FxHashMap, FxHashSet};
use static_init::dynamic;
use utils::implvec;

mod ind_cca;
mod enc_kp;
mod mutils;
// mod grammar;

define_language! {
    enum CCSA {
        Const(Symbol),
        "nonce" = Nonce(Id),
        "enc" = Enc([Id; 3]),
        "dec" = Dec([Id; 2]),
        "pk" = Pk(Id),
        "ite" =  Ite([Id; 3]),
        "tuple" = Tuple([Id; 2]),
        "p1" = Proj1(Id),
        "p2" = Proj2(Id),
        "eq" = Eq([Id; 2]),
        "length" = Length(Id),
        "zeroes" = Zeroes(Id),
        "mtrue" = True,
        "mfalse" = False,
        "eta" = Eta,
        "input" = Input(Id),
        "equiv" = Equiv(Id),
    }
}

macro_rules! mk_consts {
    ($($id:ident)*) => {
        $(paste::paste! {mk_consts!(@  [<$id:upper>]);})*
    };
    (@ $id:ident) => {
        pub const $id: &str = std::stringify!($id);
    };
}

mk_consts!(nonce enc dec pl ite tuple p1 p2 eq length zeroes mtrue mfalse etq input);

fn make_general_rules() -> Vec<Rewrite<CCSA, ()>> {
    vec![
        rewrite!("simpl-tuple-1"; "(p1 (tuple ?a ?b))" => "?a"),
        rewrite!("simpl-tuple-1"; "(p2 (tuple ?a ?b))" => "?a"),
        rewrite!("simpl-dec"; "(dec (enc ?m ?r (pk ?k)), ?k)" => "?m"),
        rewrite!("ite-base-1"; "(ite mtrue ?a ?b)" => "?a"),
        rewrite!("ite-base-2"; "(ite mfalse ?a ?b)" => "?b"),
        rewrite!("ite-same"; "(ite ?c ?a ?a)" => "?a"),
        rewrite!("ite-eq-1"; "(ite (eq ?a ?b) ?a ?b)" => "?a"),
        rewrite!("ite-eq-1"; "(ite (eq ?a ?b) ?a ?b)" => "?b"),
        rewrite!("eq-refl"; "(eq ?a ?a)" => "mtrue"),
        rewrite!("eq-sym"; "(eq ?a ?b)" => "(eq ?b ?a)"),
        rewrite!("length-nonce"; "(length (nonce ?x))"  => "eta"),
        rewrite!("length-zeroes"; "(length (zeroes (length ?x)))" => "(length ?x)"),
    ]
}

fn mk_term(k: &str, pgr: &str) -> RecExpr<CCSA> {
    format!("(ite
        (eq (p1 (input {pgr})) (pk (nonce kb)))
        (ite
            (eq (length (tuple (nonce nb) (nonce nb))) (length (tuple (p2 (input {pgr})) (nonce nb))))
            (enc (tuple (p2 (input {pgr})) (nonce nb)) (nonce r) (pk (nonce {k})))
        )
        (enc (tuple (p2 (input {pgr})) (nonce nb)) (nonce r) (pk (nonce {k})))
    )").parse().unwrap()
}

fn mk_bubble_rules<'a>(funs: implvec!((&'a str, u32))) -> Vec<Rewrite<CCSA, ()>> {
    struct Var(u32);
    impl Display for Var {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "?var{}", self.0)
        }
    }

    fn vars(start: u32, arity: u32) -> impl Iterator<Item = Var> {
        (start..(start + arity)).map(Var)
    }

    let vec = funs.into_iter().collect_vec();
    let iter1 = vec.iter().map(|(f, arity)| {
        let premise: Pattern<CCSA> = format!(
            "(ite ?c ({f} {}) ({f} {})",
            vars(0, *arity).join(" "),
            vars(*arity, *arity).join(" ")
        )
        .parse()
        .unwrap();
        let args_conclusion = izip!(vars(0, *arity), vars(*arity, 0))
            .map(|(v1, v2)| format!("(ite ?c {v1} {v2})"))
            .join(" ");
        let conclusion: Pattern<CCSA> = format!("({f} {args_conclusion})").parse().unwrap();
        Rewrite::new(format!("ite-bubble-down-{f}"), premise, conclusion).unwrap()
    });
    let iter2 = vec.iter().map(|(f, arity)| {
        let premise: Pattern<CCSA> = format!(
            "(ite ?c ({f} {}) ({f} {})",
            vars(0, *arity).join(" "),
            vars(*arity, *arity).join(" ")
        )
        .parse()
        .unwrap();
        let args_conclusion = izip!(vars(0, *arity), vars(*arity, 0))
            .map(|(v1, v2)| format!("(ite ?c {v1} {v2})"))
            .join(" ");
        let conclusion: Pattern<CCSA> = format!("({f} {args_conclusion})").parse().unwrap();
        Rewrite::new(format!("ite-bubble-up-{f}"), conclusion, premise).unwrap()
    });
    chain!(iter1, iter2).collect()
}

#[dynamic]
static EQUIV_PATTERN: Pattern<CCSA> = "(equiv ?a)".parse().unwrap();

#[dynamic]
static ENC_PATTERN: Pattern<CCSA> = "(enc ?m (nonce ?r) (pk (nonce ?k)))".parse().unwrap();

fn get_equiv_eclass(egraph: &EGraph<CCSA, ()>) -> impl Iterator<Item = &EClass<CCSA, ()>> {
    EQUIV_PATTERN
        .search(egraph)
        .into_iter()
        .map(|SearchMatches { eclass, .. }| &egraph[eclass])
}

fn get_enc_eclass(egraph: &EGraph<CCSA, ()>) -> impl Iterator<Item = (&EClass<CCSA, ()>, Subst)> {
    ENC_PATTERN.search(egraph).into_iter().flat_map(
        move |SearchMatches { eclass, substs, .. }| {
            substs.into_iter().map(move |s| (&egraph[eclass], s))
        },
    )
}

fn enc_kp(graph: &mut EGraph<CCSA, ()>) {}

fn enc_kp_once(egraph: &EGraph<CCSA, ()>, eclass: &EClass<CCSA, ()>, subst: Subst) {
    let k = egraph
        .lookup(CCSA::Nonce(*subst.get("?k".parse().unwrap()).unwrap()))
        .unwrap();
    let r = egraph
        .lookup(CCSA::Nonce(*subst.get("?r".parse().unwrap()).unwrap()))
        .unwrap();
    let m = *subst.get("?m".parse().unwrap()).unwrap();

    let pk_k = egraph
        .lookup(CCSA::Pk(r))
        .expect("pk(k) is not in the graph");
}

fn is_nonce(egraph: &EGraph<CCSA, ()>, id: Id) -> bool {
    egraph[id].iter().any(|l| match l {
        CCSA::Nonce(_) => true,
        _ => false,
    })
}

impl CCSA {
    pub fn is_equiv(&self) -> bool {
        match self {
            CCSA::Equiv(_) => true,
            _ => false,
        }
    }
}

pub trait TermRepr<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    fn add_to_graph(self, egraph: &mut EGraph<L, N>) -> Id;
}

impl<L, N> TermRepr<L, N> for  RecExpr<L>
where
    L: Language,
    N: Analysis<L>,
{
    fn add_to_graph(self, egraph: &mut EGraph<L, N>) -> Id {
        egraph.add_expr(&self)
    }
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord, Clone)]
pub struct Union<U> {
    old: Id, new: U, reason: Cow<'static, str>
}

pub trait Rule<L, N> where L:Language, N: Analysis<L> {
    type T: TermRepr<L, N>;

    fn find(&self, egraph: &EGraph<L, N>) -> impl Iterator<Item = Union<Self::T>>;
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Default)]
enum SearchEnum {
    #[default]
    Current,
    Checked,
    CheckedFalse,
}

impl From<bool> for SearchEnum {
    fn from(value: bool) -> Self {
        if value {
            Self::Checked
        } else {
            Self::CheckedFalse
        }
    }
}

// #[derive(Debug, Clone, Default)]
// struct SearchState(FxHashMap<Id, IdSearchState>);

// #[derive(Debug, Clone)]
// struct IdSearchState(FxHashSet<Id>);

// impl Default for IdSearchState {
//     fn default() -> Self {
//         todo!()
//     }
// }

// impl<'a> IntoIterator for &'a IdSearchState {
//     type Item = &'a Id;

//     type IntoIter = <&'a FxHashSet<Id> as IntoIterator>::IntoIter ;

//     fn into_iter(self) -> Self::IntoIter {
//         self.0.iter()
//     }
// }

// impl IdSearchState {
//     pub fn set_depends_on(&mut self, nonces: &FxHashSet<Id>) {
//         FxHashSet::
//         self.0.intersection()
//     }
// }

// impl SearchState {
//     pub fn push(&mut self, id: Id) -> &mut IdSearchState {
//         self.0.entry(id).or_default()
//     }
// }

// fn find_next_key(k: Id, t: &CCSA) -> impl Iterator<Item = &Id> {
//     match t {
//         CCSA::Dec(args) if args[1] == k => args[..1].iter(),
//         CCSA::Input(_) => [].iter(), // TODO
//         _ => t.children().iter(),
//     }
// }

// fn not_subterm_down<'a, F, I>(
//     egraph: &'a EGraph<CCSA, ()>,
//     search_state: &mut SearchState,
//     find_next: &F,
//     ignore: &'a [Id],
//     m: Id,
//     current: Id,
// ) -> bool
// where
//     F: Fn(Id, &'a CCSA) -> I,
//     I: Iterator<Item = &'a Id>,
// {
//     if current == m {
//         false
//     } else if let Some(b) = search_state.get_bool(&current) {
//         b
//     } else {
//         search_state.push_current(current);
//         let res = ignore.contains(&current) || {
//             let eclass = &egraph[current];
//             let mut iter = eclass.iter().flat_map(|t| find_next(m, t)).peekable();
//             iter.peek().is_none()
//                 || iter.any(|&id| not_subterm_down(egraph, search_state, find_next, ignore, m, id))
//         };
//         search_state.set_bool(current, res)
//     }
// }

// fn not_subterm_up<'a, F, I>(
//     egraph: &'a EGraph<CCSA, ()>,
//     search_state: &mut SearchState,
//     find_next: &F,
//     ignore: &'a [Id],
//     m: Id,
//     goal: Id,
//     current: Id,
// ) -> bool
// where
//     F: Fn(Id, &'a CCSA) -> I,
//     I: Iterator<Item = &'a Id>,
// {
//     if current == m {
//         false
//     } else if let Some(b) = search_state.get_bool(&current) {
//         b
//     } else {
//         search_state.push_current(current);
//         let res = ignore.contains(&current) || {
//             egraph[current].parents().any(|(ast, parent_id)| {
//                 (parent_id == goal
//                     || not_subterm_up(egraph, search_state, find_next, ignore, m, goal, parent_id))
//                     && (ast
//                         .children()
//                         .iter()
//                         .filter(|&&id| id != current)
//                         .all(|&sibling| {
//                             not_subterm_down(egraph, search_state, find_next, ignore, m, sibling)
//                         }))
//             })
//         };
//         search_state.set_bool(current, res)
//     }
// }

fn main() {
    let mut runner: Runner<CCSA, ()> = Runner::new(Default::default());

    let start = mk_term("ka", "pgrm1");
    let end = mk_term("ka2", "pgrm2");
    // runner.egraph.union(id1, id2)
}
