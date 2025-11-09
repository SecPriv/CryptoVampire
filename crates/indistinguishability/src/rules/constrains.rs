use egg::{Analysis, EGraph, MultiPattern, Rewrite};
use itertools::{Itertools, chain, izip};
use rustc_hash::{FxHashMap, FxHashSet};
use utils::{dynamic_iter, ebreak_if, ereturn_if};

use crate::{
    Lang, MSmt, MSmtFormula, Problem,
    problem::{BoundStep, ConstrainOp, Constrains, CurrentStep, PAnalysis},
    rexp, smt,
    terms::{HAPPENS, INIT, IS_INDEX, LEQ, LT, PRED, RecFOFormula, TRUE, Variable},
};

macro_rules! bind {
    ($s1:ident($a1:ident..) $op:ident $s2:ident($a2:ident..)) => {
        Constrains {
            $op,
            arg1: BoundStep {
                head: $s1,
                args: $a1,
            },
            arg2: BoundStep {
                head: $s2,
                args: $a2,
            },
        }
    };
}

pub fn modify_egraph<'pbl>(egraph: &mut EGraph<Lang, PAnalysis<'pbl>>) {
    let CurrentStep { idx, args } = egraph.analysis.pbl().current_step().unwrap();
    let cf = egraph.analysis.pbl().get_step_fun(*idx).unwrap().clone();

    let args = args.iter().map(|f| rexp!(f));
    let s = rexp!((cf #args*));

    let hid = egraph.add_expr(&s.as_egg_ground());
    let trueid = egraph.add(TRUE.app_id([]));
    egraph.union(hid, trueid);

    let hpridid = egraph.add_expr(&rexp!((PRED #s)).as_egg_ground());
    egraph.union(hpridid, trueid);
}

pub fn mk_smt(pbl: &Problem) -> impl Iterator<Item = MSmt> {
    pbl.constrains()
        .iter()
        .flat_map(|c| mk_smt_constrain_one(pbl, c))
        .map(|s| MSmt::Assert(s))
}

pub fn mk_rewrite<N: Analysis<Lang>>(pbl: &Problem) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    chain![
        mk_rewrite_static(),
        pbl.constrains().iter().flat_map(|c| mk_rewrite_one(pbl, c))
    ]
}

fn mk_smt_constrain_one(
    _: &Problem,
    bind!(s1(a1..) op s2(a2..)): &Constrains,
) -> impl Iterator<Item = MSmtFormula> {
    let vars_iter = chain![a1, a2].unique().cloned();
    let args1 = a1.iter().map::<MSmtFormula, _>(|v| smt!(#v));
    let args2 = a1.iter().map::<MSmtFormula, _>(|v| smt!(#v));
    match op {
        ConstrainOp::LessThan => {
            [smt!((forall #(vars_iter) (LT (s1 #args1*) (s2 #args2*))))].into_iter()
        }
        ConstrainOp::Exclude => [smt!((forall #(vars_iter)
          (=>
            (and (HAPPENS (s1 #(args1.clone())*)) (HAPPENS (s2 #(args2.clone())*)))
            (= (s1 #args1*) (s2 #args2*)))))]
        .into_iter(),
    }
}

decl_vars!(const TRUTH_VAR:Bool);

fn mk_rewrite_one<N: Analysis<Lang>>(
    pbl: &Problem,
    bind!(s1(a1..) op s2(a2..)): &Constrains,
) -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    let CurrentStep { idx, args } = pbl.current_step().unwrap();
    let cf = pbl.get_step_fun(*idx).unwrap();
    let argscf = args.iter().map(|f| rexp!(f)).collect_vec();
    match op {
        ConstrainOp::LessThan if s2 == cf => {
            let argmap: FxHashMap<_, _> = izip!(a2, &argscf).collect();
            let argss1 = a1.iter().map::<RecFOFormula, _>(|v| {
                if let Some(&a) = argmap.get(&v) {
                    rexp!(#a)
                } else {
                    rexp!(#v)
                }
            });
            let vars = a1.iter().filter(|v| !argmap.contains_key(v));

            let premise = MultiPattern::new(
                chain![
                    [(TRUTH_VAR.as_egg(), rexp!(true).as_egg_var())],
                    vars.map(|v| { (v.as_egg(), rexp!((IS_INDEX #v)).as_egg_var()) })
                ]
                .collect(),
            );

            let conclusion = MultiPattern::new(vec![(
                TRUTH_VAR.as_egg(),
                rexp!((LT (s1 #argss1*) (s2 #argscf*))).as_egg_var(),
            )]);
            Rewrite::new(format!("constrain {s1} < {s2}"), premise, conclusion).ok()
        }
        ConstrainOp::Exclude if s1 == cf || s2 == cf => {
            let (s1, a1, a2) = if s1 == cf { (s2, a2, a1) } else { (s1, a1, a2) };
            let argmap: FxHashMap<_, _> = izip!(a2, &argscf).collect();
            let argss1 = a1.iter().map::<RecFOFormula, _>(|v| {
                if let Some(&a) = argmap.get(&v) {
                    rexp!(#a)
                } else {
                    rexp!(#v)
                }
            });
            let vars = a1.iter().filter(|v| !argmap.contains_key(v));

            let premise = MultiPattern::new(
                chain![
                    [(TRUTH_VAR.as_egg(), rexp!(false).as_egg_var())],
                    vars.map(|v| { (v.as_egg(), rexp!((IS_INDEX #v)).as_egg_var()) })
                ]
                .collect(),
            );
            let conclusion = MultiPattern::new(vec![(
                TRUTH_VAR.as_egg(),
                rexp!((HAPPENS (s1 #argss1*))).as_egg_var(),
            )]);
            Rewrite::new(format!("constrain {s1} <> {s2}"), premise, conclusion).ok()
        }
        _ => None,
    }
    .into_iter()
}

fn mk_rewrite_static<N: Analysis<Lang>>() -> impl Iterator<Item = egg::Rewrite<Lang, N>> {
    decl_vars![t, t1, t2, a, b, c, v1, p, n, u, v];

    mk_many_rewrites! {
     ["leq refl"] (LEQ #t #t) => true.
     ["leq pred"] (LEQ (PRED #t) #t) => true.
     ["leq pred rev"] (LEQ #t (PRED #t)) => false.
     ["lt pred rev"] (LT #t (PRED #t)) => false.
     ["lt self rev"] (LT #t  #t) => false.

     ["pred init"] (PRED INIT) => INIT.

     ["happens leq"]
     (#v1 = (HAPPENS #t1), #v1 = (LT  #t2 #t1), #v1 = true) => (#v1 = (HAPPENS #t2)).

     ["lt to leq"]
     (#v1 = (LT  #t2 #t1), #v1 = true) => (#v1 = (LEQ #t2 #t1)).

    }
    .into_iter()
}
