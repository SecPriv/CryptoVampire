use egg::{Analysis, EGraph, MultiPattern, Pattern, Rewrite};
use itertools::{Itertools, chain, izip};
use rustc_hash::FxHashMap;
use utils::ereturn_if;

use super::SMT_OPTIONS;
use crate::libraries::Library;
use crate::libraries::utils::{EggRewriteSink, SmtSink};
use crate::problem::cache::Context;
use crate::problem::{BoundStep, ConstrainOp, Constrains, CurrentStep, PAnalysis};
use crate::terms::{
    CURRENT_STEP, Formula, FormulaVariableIter, HAPPENS, INIT, IS_INDEX, LEQ, LT, PRED, TEQ, TRUE,
};
use crate::{Lang, MSmt, MSmtFormula, MSmtParam, Problem, rexp, smt};

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

pub struct ConstrainsLib;

impl Library for ConstrainsLib {
    fn add_smt<'a>(&self, pbl: &mut Problem, ctx: &Context, sink: &mut impl SmtSink<'a>) {
        ereturn_if!(ctx.using_cache);

        sink.comment(pbl, &SMT_OPTIONS, "Constrains");

        sink.reserve(pbl.constrains().len());
        for constrain in pbl.constrains() {
            add_smt_constrain_one(pbl, constrain, sink);
        }
    }

    fn add_egg_rewrites<N: Analysis<Lang>>(
        &self,
        pbl: &mut Problem,
        sink: &mut impl EggRewriteSink<N>,
    ) {
        add_rewrite_static(sink);

        for c in pbl.constrains() {
            add_rewrite_one(pbl, c, sink)
        }
    }

    fn modify_egraph<'a>(&self, egraph: &mut EGraph<Lang, PAnalysis<'a>>) {
        let CurrentStep { idx, args } = egraph.analysis.pbl().current_step().unwrap();
        let cf = egraph.analysis.pbl().get_step_fun(*idx).unwrap().clone();

        let args = args.iter().map(|f| rexp!(f));
        let s = rexp!((cf #args*));

        let hid = egraph.add_expr(&rexp!((HAPPENS #s)).as_egg_ground());
        let trueid = egraph.add(TRUE.app_id([]));
        egraph.union(hid, trueid);

        let cs = egraph.add(CURRENT_STEP.app_id([]));
        let s = egraph.add_expr(&s.as_egg_ground());
        egraph.union(s, cs);

        // let hpridid = egraph.add_expr(&rexp!((HAPPENS (PRED #s))).as_egg_ground());
        // egraph.union(hpridid, trueid);
    }
}

fn add_smt_constrain_one<'a>(
    pbl: &Problem,
    bind!(s1(a1..) op s2(a2..)): &Constrains,
    sink: &mut impl SmtSink<'a>,
) {
    debug_assert_eq!(s1.arity(), a1.len());
    debug_assert_eq!(s2.arity(), a2.len());
    let vars_iter = chain![a1, a2].unique().cloned();
    let args1 = a1.iter().map::<MSmtFormula<'a>, _>(|v| smt!(#v));
    let args2 = a2.iter().map::<MSmtFormula<'a>, _>(|v| smt!(#v));
    sink.assert_one(
        pbl,
        &SMT_OPTIONS,
        match op {
            ConstrainOp::LessThan => {
                smt!((forall #(vars_iter) (LT (s1 #args1*) (s2 #args2*))))
            }
            ConstrainOp::Exclude => smt!((forall #(vars_iter)
          (=>
            (and (HAPPENS (s1 #(args1.clone())*)) (HAPPENS (s2 #(args2.clone())*)))
            (= (s1 #args1*) (s2 #args2*))))),
        },
    )
}

decl_vars!(const TRUTH_VAR:Bool);

fn add_rewrite_one<N: Analysis<Lang>>(
    pbl: &Problem,
    bind!(s1(a1..) op s2(a2..)): &Constrains,
    sink: &mut impl EggRewriteSink<N>,
) {
    let CurrentStep { idx, args } = pbl.current_step().unwrap();
    let cf = pbl.get_step_fun(*idx).unwrap();
    let argscf = args.iter().map(|f| rexp!(f)).collect_vec();
    // we need to take care of free variables. so things can get complicated
    match op {
        ConstrainOp::LessThan if s2 == cf => {
            let argmap: FxHashMap<_, _> = izip!(a2, &argscf).collect();
            let argss1 = a1.iter().map::<Formula, _>(|v| {
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
            sink.add_egg_rewrite(
                Rewrite::new(format!("constrain {s1} < {s2}"), premise, conclusion).unwrap(),
            )
        }
        // ConstrainOp::LessThan => {
        //     // let vars = chain![a1.iter(), a2.iter()].cloned();
        //     let a1 = a1.iter().into_formula_iter();
        //     let a2 = a2.iter().into_formula_iter();
        //     let premise = rexp!((LT (s1 #a1*) (s2 #a2*)));
        //     let conclusion = rexp!(true);

        //     sink.add_egg_rewrite(Rewrite::new(
        //         format!("constraint gen {s1} < {s2}"),
        //         Pattern::from(&premise),
        //         Pattern::from(&conclusion),
        //     ).unwrap());
        // }
        ConstrainOp::Exclude if s1 == cf || s2 == cf => {
            let (s1, a1, a2) = if s1 == cf { (s2, a2, a1) } else { (s1, a1, a2) };
            let argmap: FxHashMap<_, _> = izip!(a2, &argscf).collect();
            let argss1 = a1.iter().map::<Formula, _>(|v| {
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
            sink.add_egg_rewrite(
                Rewrite::new(format!("constrain {s1} <> {s2}"), premise, conclusion).unwrap(),
            )
        }
        _ => {}
    }
}

fn add_rewrite_static<N: Analysis<Lang>>(sink: &mut impl EggRewriteSink<N>) {
    decl_vars![t, t1, t2, v1];

    sink.extend_egg_rewrites(mk_many_rewrites! {
        ["leq refl"] (LEQ #t #t) => true.
        ["leq pred"] (LEQ (PRED #t) #t) => true.
        ["leq pred rev"] (LEQ #t (PRED #t)) => false.
        ["lt pred rev"] (LT #t (PRED #t)) => false.
        ["lt self rev"] (LT #t  #t) => false.

        ["pred init"] (PRED INIT) => INIT.

        ["happens leq"]
        (#v1 = (HAPPENS #t1), #v1 = (LT  #t2 #t1), #v1 = true) => (#v1 = (HAPPENS #t2)).

        ["lt to leq"]
        (#v1 = (LT  #t2 #t1), #v1 = true) => (#v1 = (LEQ #t2 (PRED #t1))).

        ["leq trans"]
        (#v1 = (LEQ #t1 #t2), #v1 = (LEQ #t2 #t), #v1 = true) => (#v1 = (LEQ #t1 #t)).

        ["lt trans"]
        (#v1 = (LT #t1 #t2), #v1 = (LT #t2 #t), #v1 = true) => (#v1 = (LT #t1 #t)).
    })
}
