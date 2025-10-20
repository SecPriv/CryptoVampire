// pub mod basic_hash {
//     use std::ops::Deref;

//     use egg::Pattern;
//     use golgge::PrologRule;

//     use crate::protocol::test::basic_hash::MFunction;
//     use crate::terms::utils::type_check;
//     use crate::terms::{
//         EMPTY, EQUIV, FROM_BOOL, MACRO_EXEC, MACRO_FRAME, MITE, NONCE, PRED, TUPLE, UNFOLD_FRAME,
//     };
//     use crate::{Lang, Problem, decl_fun, rexp};

//     pub fn mk_prf_rule(pbl: &mut Problem, funs: &MFunction) -> PrologRule<Lang> {
//         let n0 = decl_fun!(pbl; "n0": (Index, Index, Protocol) -> Nonce);
//         let MFunction { tag, n, p1, p2, .. } = funs;

//         let input: Pattern<Lang> = Pattern::new(
//             rexp!((EQUIV #0 #1 (UNFOLD_FRAME (tag #2 #3) p1) (UNFOLD_FRAME (tag #2 #3) p2)))
//                 .to_vec()
//                 .into(),
//         );
//         let dep: Pattern<Lang> = Pattern::new(
//             rexp!((EQUIV #0 #1
//               (TUPLE
//                   (TUPLE
//                       (FROM_BOOL (MACRO_EXEC (tag #2 #3) p1))
//                       (MITE (MACRO_EXEC (tag #2 #3) p1)
//                         (TUPLE (NONCE (n #2 #3)) (NONCE (n0 #2 #3 p1)))
//                         EMPTY))
//                   (MACRO_FRAME (PRED (tag #2 #3)) p1))
//               (TUPLE
//                   (TUPLE
//                       (FROM_BOOL (MACRO_EXEC (tag #2 #3) p2))
//                       (MITE (MACRO_EXEC (tag #2 #3) p2)
//                         (TUPLE (NONCE (n #2 #3)) (NONCE (n0 #2 #3 p2)))
//                         EMPTY))
//                   (MACRO_FRAME (PRED (tag #2 #3)) p2))
//             ))
//             .to_vec()
//             .into(),
//         );

//         assert!(type_check(input.ast.deref()));
//         assert!(type_check(dep.ast.deref()));

//         PrologRule::builder()
//             .input(input)
//             .deps([dep])
//             .name("euf-cma")
//             .build()
//             .unwrap()
//     }
// }
