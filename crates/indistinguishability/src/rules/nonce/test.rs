// #[allow(unused_imports)]
// use cryptovampire_smt::{Smt, SmtFormula};
// #[allow(unused_imports)]
// use egg::{Analysis, EGraph, Id, Runner};
// #[allow(unused_imports)]
// use itertools::Itertools;

// use crate::problem::PAnalysis;
// use crate::problem::test::basic_hash::mk_pblm;
// use crate::rules::default_rewrites;
// use crate::rules::nonce::Nonce;
// use crate::rules::utils::fresh::{Mode, RefFormulaBuilder};
// use crate::terms::utils::convert_to_ground_rexp;
// use crate::terms::{Function, HAPPENS, MACRO_COND, MACRO_INPUT, MACRO_MSG, RecFOFormula, Sort};
// use crate::{Lang, Problem, decl_fun, init_logger, rexp};

// fn mk_egraph<'a>(pbl: &'a mut Problem) -> (EGraph<Lang, PAnalysis<'a>>, Id, Id, Id) {
//     let rw = default_rewrites::mk_rewrites(pbl).collect_vec();

//     let i = decl_fun!(pbl; "i": () -> Index);
//     let j = decl_fun!(pbl; "j": () -> Index);
//     let p1 = pbl.protocols()[0].name().clone();
//     let tag = pbl.function.get("tag").unwrap();
//     let rf = pbl.function.get("Rf").unwrap();

//     let mut egraph = EGraph::new(PAnalysis::builder().pbl(pbl).build());
//     let input_tag =
//         egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_INPUT (tag i j) p1))).unwrap());
//     let cond_rf = egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_COND (rf i) p1))).unwrap());
//     let msg_tag =
//         egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_MSG (tag i j) p1))).unwrap());
//     let ht = egraph.add_expr(&convert_to_ground_rexp(rexp!((HAPPENS (tag i j)))).unwrap());
//     let hrf = egraph.add_expr(&convert_to_ground_rexp(rexp!((HAPPENS (rf i)))).unwrap());
//     let mtrue = egraph.add_expr(&convert_to_ground_rexp(rexp!(true)).unwrap());
//     egraph.union(ht, mtrue);
//     egraph.union(hrf, mtrue);

//     // egraph.rebuild();

//     let runner: Runner<Lang, _> = Runner::new_with_egraph(egraph);
//     let runner = runner.run(&rw);

//     tr!("report: {}", runner.report());

//     (runner.egraph, cond_rf, msg_tag, input_tag)
// }

// #[test]
// fn subterm_cond_rf() {
//     init_logger();
//     let mut pbl = mk_pblm().0;
//     let (egraph, cond_rf, _, _) = mk_egraph(&mut pbl);
//     let n = egraph.analysis.pbl().function.get("n").unwrap();
//     let n = Nonce::new_from_args(n, ["i", "j"].map(|s| RecFOFormula::Var(s.parse().unwrap())));

//     let builder = RefFormulaBuilder::builder().mode(Mode::And).build();
//     n.search_egraph(&egraph, builder.clone(), cond_rf, Default::default());

//     let f = builder.into_inner().unwrap().into_formula();
//     let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

//     println!("formula: {smt}");
//     panic!("wrong result")
// }

// #[test]
// fn subterm_msg_tag() {
//     init_logger();
//     let mut pbl = mk_pblm().0;
//     let (egraph, _, _, msg_tag) = mk_egraph(&mut pbl);
//     let pbl = egraph.analysis.pbl();
//     let n = pbl.function.get("n").unwrap();
//     let i = pbl.function.get("i").unwrap();
//     let j = pbl.function.get("j").unwrap();
//     let _ = pbl;
//     let n = Nonce::new_from_args(
//         n,
//         [i, j].map(|x| RecFOFormula::App {
//             head: x,
//             args: vec![],
//         }),
//     );

//     let builder = RefFormulaBuilder::builder().mode(Mode::And).build();
//     n.search_egraph(&egraph, builder.clone(), msg_tag, Default::default());

//     let f = builder.into_inner().unwrap().into_formula();
//     let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

//     println!("formula: {smt}")
// }
