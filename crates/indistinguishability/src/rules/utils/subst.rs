use egg::{
    Analysis, ConditionEqual, ConditionNot, ConditionalApplier, ENodeOrVar, Id, Pattern,
    PatternAst, Rewrite,
};
use itertools::{Itertools, chain, izip};
use logic_formula::egg::SimpleDiscriminant;
use utils::dynamic_iter;

use crate::problem::CurrentStep;
use crate::rules::utils::generate_rule_vars;
use crate::terms::{Function, MACRO_EXEC, MACRO_FRAME, NONCE, PRED, SUBSTITUTION, Sort};
use crate::{Lang, Problem, rexp};

/// you should **not** use these rule with the other ones
pub fn mk_subst_rw<'a, N: Analysis<Lang>>(
    pbl: &'a Problem,
) -> impl Iterator<Item = Rewrite<Lang, N>> + use<'a, N> {
    chain![[mk_rw_self()], mk_rw_base(pbl), mk_rec_shortcut(pbl)]
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

fn mk_rec_shortcut<N: Analysis<Lang>>(pbl: &Problem) -> impl Iterator<Item = Rewrite<Lang, N>> {
    dynamic_iter!(Ret; Empty:A, Full:B);

    if let Some(CurrentStep { idx, args }) = pbl.current_step()
        && *idx != 0
        && let Some(s) = pbl.get_step_name(*idx)
    {
        let n = args.len();
        let [x, y, p] = ::std::array::from_fn(|i| [ENodeOrVar::Var((i as u32).into())]);

        let fun: PatternAst<Lang> = chain![
            args.iter().map(|f: &Function| f.app_id([])),
            [s.app_id((0..n).map(Id::from)), PRED.app_id([n.into()])]
        ]
        .map(ENodeOrVar::ENode)
        .collect();
        Ret::Full(
            [&MACRO_EXEC, &MACRO_FRAME]
                .map(|mf| {
                    let m = mf.app_var(&[fun.as_ref(), &p]);
                    let premise = SUBSTITUTION.app_var(&[m.as_ref(), &x, &y]);
                    Rewrite::new(
                        format!("subst_macro {mf}"),
                        Pattern::new(premise),
                        Pattern::new(m),
                    )
                    .unwrap()
                })
                .into_iter(),
        )
    } else {
        Ret::Empty(::std::iter::empty())
    }
}

/// substitution for regular functions
/// ```text
/// subst(f(x1,...,xn), x, y) -> f(subst(x1, x, y),...,subst(xn,x,y))
/// ```
fn mk_rw_one<N: Analysis<Lang>>(fun: Function) -> Rewrite<Lang, N> {
    let (vars, ref ov @ [ref x, ref y]) = generate_rule_vars(&fun);
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
        let args = izip!(fun.signature.inputs.iter(), vars)
            .map(|(s, v)| match s {
                Sort::Bitstring | Sort::Bool => {
                    SUBSTITUTION.app_var(&[[v], [x.clone()], [y.clone()]])
                }
                Sort::Any | Sort::Index | Sort::Time | Sort::Protocol | Sort::Nonce => {
                    vec![v].into()
                }
            })
            .collect_vec();
        let a = fun.app_var(&args);
        let b: PatternAst<Lang> = [x.clone()].into_iter().collect();
        ConditionNot(ConditionEqual::new(Pattern::from(a), b.into()))
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
        .filter(|f| (!f.is_special_subterm()) || f.is_if_then_else())
        .cloned()
        .map(mk_rw_one)
}
