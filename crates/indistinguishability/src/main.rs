use std::{borrow::Cow, default, env::vars, fmt::Display, process::exit};

use egg::*;
use enc_kp::EnkKp;
use ind_cca::IndCCA2;
use itertools::{chain, izip, Itertools};
use rustc_hash::{FxHashMap, FxHashSet};
use static_init::dynamic;
use utils::implvec;

mod enc_kp;
mod ind_cca;
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
        rewrite!("simpl-tuple-2"; "(p2 (tuple ?a ?b))" => "?a"),
        rewrite!("simpl-dec"; "(dec (enc ?m ?r (pk ?k)) ?k)" => "?m"),
        rewrite!("ite-base-1"; "(ite mtrue ?a ?b)" => "?a"),
        rewrite!("ite-base-2"; "(ite mfalse ?a ?b)" => "?b"),
        rewrite!("ite-same"; "(ite ?c ?a ?a)" => "?a"),
        rewrite!("ite-eq-1"; "(ite (eq ?a ?b) ?a ?b)" => "?a"),
        rewrite!("ite-eq-2"; "(ite (eq ?a ?b) ?a ?b)" => "?b"),
        rewrite!("eq-refl"; "(eq ?a ?a)" => "mtrue"),
        rewrite!("eq-sym"; "(eq ?a ?b)" => "(eq ?b ?a)"),
        rewrite!("length-nonce"; "(length (nonce ?x))"  => "eta"),
        rewrite!("length-zeroes"; "(length (zeroes (length ?x)))" => "(length ?x)"),
    ]
}

fn mk_term(k: &str, pgr: &str) -> RecExpr<CCSA> {
    format!("(equiv (ite
        (eq (p1 (input {pgr})) (pk (nonce kb)))
        (ite
            (eq (length (tuple (nonce nb) (nonce nb))) (length (tuple (p2 (input {pgr})) (nonce nb))))
            (enc (tuple (p2 (input {pgr})) (nonce nb)) (nonce r) (pk (nonce {k})))
            (enc (tuple (nonce nb) (nonce nb)) (nonce r) (pk (nonce {k})))
        )
        (enc (tuple (p2 (input {pgr})) (nonce nb)) (nonce r) (pk (nonce {k})))
))").parse().unwrap()
}

fn nonces(n: &[&str]) -> Vec<RecExpr<CCSA>> {
    n.iter()
        .map(|n| format!("(nonce {n})").parse().unwrap())
        .collect()
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
            "(ite ?c ({f} {}) ({f} {}))",
            vars(0, *arity).join(" "),
            vars(*arity, *arity).join(" ")
        )
        .parse()
        .unwrap();
        let args_conclusion = izip!(vars(0, *arity), vars(*arity, *arity))
            .map(|(v1, v2)| format!("(ite ?c {v1} {v2})"))
            .join(" ");
        let conclusion: Pattern<CCSA> = format!("({f} {args_conclusion})").parse().unwrap();
        Rewrite::new(format!("ite-bubble-down-{f}"), premise, conclusion).unwrap()
    });
    let iter2 = vec.iter().map(|(f, arity)| {
        let premise: Pattern<CCSA> = format!(
            "(ite ?c ({f} {}) ({f} {}))",
            vars(0, *arity).join(" "),
            vars(*arity, *arity).join(" ")
        )
        .parse()
        .unwrap();
        let args_conclusion = izip!(vars(0, *arity), vars(*arity, *arity))
            .map(|(v1, v2)| format!("(ite ?c {v1} {v2})"))
            .join(" ");
        let conclusion: Pattern<CCSA> = format!("({f} {args_conclusion})").parse().unwrap();
        println!("{premise}");
        println!("{conclusion}");
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
    egraph[id].iter().any(|l| matches!(l, CCSA::Nonce(_)))
}

impl CCSA {
    pub fn is_equiv(&self) -> bool {
        matches!(self, CCSA::Equiv(_))
    }
}

pub trait TermRepr<L, N>
where
    L: Language,
    N: Analysis<L>,
{
    fn add_to_graph(self, egraph: &mut EGraph<L, N>) -> Id;
}

impl<L, N> TermRepr<L, N> for RecExpr<L>
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
    old: Id,
    new: U,
    reason: Cow<'static, str>,
}

pub trait Rule<L, N>
where
    L: Language,
    N: Analysis<L>,
{
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

fn main() {
    let runner: Runner<CCSA, ()> = Runner::new(Default::default());

    let start = mk_term("ka", "pgrm1");
    let end = mk_term("ka2", "pgrm2");

    let funs = [
        ("enc", 3),
        ("dec", 2),
        ("tuple", 2),
        ("p1", 1),
        ("p2", 1),
        ("eq", 2),
        ("length", 1),
        ("zeroes", 1),
    ]
    .into_iter();

    let rules = chain!(make_general_rules(), mk_bubble_rules(funs)).collect_vec();

    let mut egraph = EGraph::default().with_explanations_enabled();
    let nonces = nonces(&["ka", "ka2", "kextra", "n"])
        .into_iter()
        .map(|k| egraph.add_expr(&k))
        .collect_vec();
    let enc_kp_s = EnkKp { nonces };

    egraph.add_expr(&start);
    egraph.add_expr(&end);

    egraph.rebuild();
    let mut runner = runner.with_egraph(egraph);
    println!("initialization done, starting");

    let mut i = 0;
    loop {
        println!("---------\niteration no{i:}");
        {
            let dump = runner.egraph.dump();
            // println!("{dump:?}");
            // runner
            //     .egraph
            //     .dot()
            //     .to_pdf(format!("/tmp/{i:}.pdf"))
            //     .unwrap();
        }
        println!("checking for result...");

        if !runner.egraph.equivs(&start, &end).is_empty() {
            println!("success!");
            let explanation = runner.egraph.explain_equivalence(&start, &end);
            println!("because: {explanation}");
            exit(0)
        }
        println!("goal no reached. improving egraph...");
        runner = runner.run(&rules);
        let egraph = &runner.egraph;

        println!("\tbasic rule applied");
        let ind_cca = IndCCA2.find(egraph).collect_vec();
        println!("\tind cca found {:} instances", ind_cca.len());
        let enc_kp = enc_kp_s.find(egraph).collect_vec();
        println!("\tenc kp found {:} instances", enc_kp.len());

        println!("\tAdding new instances to the egraph");

        for Union { old, new, reason } in chain!(ind_cca, enc_kp) {
            println!(
                "kind:{reason},\nold:{},\nnew:{}\n",
                runner.egraph.id_to_expr(old).pretty(80),
                new.pretty(80)
            );
            let new = runner.egraph.add_expr(&new);
            runner.egraph.union_trusted(old, new, reason.as_ref());
        }
        println!("\trebuilding egraph");
        runner.egraph.rebuild();

        println!("\tend of loop!");
        runner.stop_reason = None;

        i += 1;
        if i > 3 {
            println!("giving up !");
            exit(2)
        }
    }
    // runner.egraph.union(id1, id2)
}
