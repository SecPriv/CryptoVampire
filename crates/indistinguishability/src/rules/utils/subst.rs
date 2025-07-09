use egg::{
    Analysis, ConditionEqual, ConditionNot, ConditionalApplier, ENodeOrVar, Id, Pattern,
    PatternAst, Rewrite, Var,
};
use itertools::{Itertools, chain};
use logic_formula::egg::SimpleDiscriminant;

use crate::{
    Lang, LangVar, Problem, rexp,
    rules::utils::generate_rule_vars,
    terms::{Function, SUBSTITUTION},
};

/// you should **not** use these rule with the other ones
pub fn mk_subst_rw<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    chain![[mk_rw_self()], mk_rw_base(pbl)]
}

fn mk_rw_self<N: Analysis<Lang>>() -> Rewrite<Lang, N> {
    let premise: PatternAst<Lang> = rexp!((SUBSTITUTION #0 #0 #1)).into_iter().collect();
    let conclusion: PatternAst<Lang> = rexp!(#1).into_iter().collect();

    Rewrite::new(
        "subst_self",
        Pattern::from(premise),
        Pattern::from(conclusion),
    )
    .unwrap()
}

/// substitution for regular functions
/// ```text
/// subst(f(x1,...,xn), x, y) -> f(subst(x1, x, y),...,subst(xn,x,y))
/// ```
fn mk_rw_one<N: Analysis<Lang>>(fun: Function) -> Rewrite<Lang, N> {
    let (vars, ref ov @ [ref x, _]) = generate_rule_vars(&fun);
    let n = vars.len();
    let premise: PatternAst<Lang> = chain![
        vars.iter().cloned(),
        ov.clone(),
        [
            fun.app_id((0..n).map_into()),
            SUBSTITUTION.app_id([n + 2, n, n + 1].map(Id::from))
        ]
        .map(ENodeOrVar::ENode)
    ]
    .collect();

    let conclusion: PatternAst<Lang> = chain![
        vars.iter().cloned(),
        ov.clone(),
        (0..n)
            .map(|i| SUBSTITUTION.app_id([i, n, n + 1].map(Id::from)))
            .map(ENodeOrVar::ENode),
        [fun.app_id((0..n).map(|i| i + n + 2).map_into()),].map(ENodeOrVar::ENode)
    ]
    .collect();
    let condition = {
        let a: PatternAst<Lang> = chain![
            vars.iter().cloned(),
            [fun.app_id((0..n).map_into()),].map(ENodeOrVar::ENode)
        ]
        .collect();
        let b: PatternAst<Lang> = [x.clone()].into_iter().collect();
        ConditionNot(ConditionEqual::new(Pattern::<Lang>::from(a), b.into()))
    };

    let conclusion = ConditionalApplier {
        condition,
        applier: Pattern::from(conclusion),
    };

    Rewrite::new(format!("msubst_{fun}"), Pattern::from(premise), conclusion).unwrap()
}

fn mk_rw_base<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    pbl.function
        .iter()
        .filter(|f| !f.is_special_subterm())
        .cloned()
        .map(mk_rw_one)
}

// use std::collections::HashMap;

// use egg::{Analysis, EGraph, Id, Language};
// use im_rc::HashSet;
// use itertools::Itertools;
// use utils::{ereturn_let, transposer::{Transposable, VecTranspose}};

// use crate::terms::Function;

// pub struct Subst {
//   pub from: Id,
//   pub to: Id,
//   pub seen: HashMap<Id, Vec<Id>>
// }

// impl Subst {
//   pub fn apply<L:Language, N:Analysis<L>, F: FnMut(L::Discriminant) -> bool>(&mut self, egraph: &mut EGraph<L, N>, skip: &mut F, current: Id) -> Vec<Id> {
//     // ereturn_let!(let Some(c) = self.seen.get(current), c);
//     if let Some(c) = self.seen.get(&current) {
//       return c.clone();
//     }
//     if current == self.from {
//       return vec![self.to];
//     }

//     let todo = egraph[current].iter().filter(|f| skip(f.discriminant())).cloned().collect_vec();
//     let mut ret = Vec::new();

//     for f in todo {
//       let children_list = f.children().iter().map(|&c| self.apply(egraph, skip, c)).collect_vec();
//       let children_list = VecTranspose::new(&children_list);

//       for children in children_list {
//         let mut nf = f.clone();
//         for (i, c) in nf.children_mut().iter_mut().enumerate() {
//           *c = *children[i];
//         }
//         ret.push(egraph.add_uncanonical(nf))
//       }
//     }

//     self.seen.insert(current, ret.clone());

//     ret
//   }
// }
