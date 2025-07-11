use std::borrow::Cow;
use std::rc::Rc;

use super::*;
use crate::problem::PAnalysis;
use crate::protocol::Step;
use crate::rules::utils::SyntaxSearcher;
use crate::rules::utils::fresh::{ Mode};
use crate::terms::formula_utils::{offset_rexpr_owned, pull_from_egraph};
use crate::terms::{
    BITE, EQ, FOBinder, FRESH_NONCE, HAPPENS, LT, MACRO_COND, MACRO_FRAME, MACRO_MSG, MITE, NONCE,
    PRED,
};
use crate::vampire::runner::VampireExec;
use crate::{
    Lang,
    rules::utils::fresh::RefFormulaBuilder,
    terms::{Function, RecFOFormula},
};
use crate::{LangVar, Problem, rexp};
use bon::Builder;
use cryptovampire_smt::{IntoSmt, Smt, SmtFormula};
use egg::{Analysis, EGraph, Id, Pattern, PatternAst, Searcher, VarExposed};
use egg::{ENodeOrVar, Language, RecExpr, Var};
use golgge::{Dependancy, Rule};
use itertools::{Itertools, chain, izip};
use logic_formula::egg::SimplLang;
use logic_formula::{Destructed, Formula, HeadSk};
use static_init::dynamic;
use utils::traits::Named;
use utils::{ereturn_if, ereturn_let, implvec};

#[dynamic]
static FRESH_NONCE_PATTERN: Pattern<Lang> = {
    rexp!((FRESH_NONCE #0 #1 #2)).into_iter().collect()
};

#[derive(Clone, Builder)]
pub struct FreshNonce {
    #[builder(into)]
    exec: Rc<VampireExec>,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for FreshNonce {
    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        let egraph = prgm.egraph_mut();
        ereturn_let!(let Some(substs) =  FRESH_NONCE_PATTERN.search_eclass(egraph, goal),Dependancy::impossible());

        let mut conditions = Vec::with_capacity(substs.substs.len());
        for subst in substs.substs {
            let [nonce, content, hypothesis] =
                [0, 1, 2].map(|i| *subst.get(Var::from_u32(i)).unwrap());
            let hypothesis = convert_id(egraph, hypothesis);
            let nonce = Nonce::builder().content_id(egraph, nonce).build();

            let builder = RefFormulaBuilder::builder().and().build();
            nonce.search_egraph(egraph, builder.clone(), content, Default::default());
            let search = builder.into_inner().unwrap().into_formula();

            conditions.push((hypothesis >> search).into_smt())
        }
        let condition = SmtFormula::Or(conditions);

        tr!("checking {condition}");
        let pbl: &mut Problem = egraph.analysis.pbl_mut();

        self.exec.run_to_dependancy(pbl, condition)
    }

    fn name(&self) -> Cow<'_, str> {
        Cow::Borrowed("fresh nonce")
    }
}
