//! Nonce freshness

use std::borrow::Cow;
use std::rc::Rc;

use crate::problem::PAnalysis;
use crate::protocol::Step;
use crate::rules::utils::SyntaxSearcher;
use crate::rules::utils::fresh::{Condition, Mode};
use crate::terms::formula_utils::{offsets_owned, pull_from_egraph};
use crate::terms::{
    BITE, EQ, FOBinder, FRESH_NONCE, HAPPENS, LT, MACRO_COND,
    MACRO_FRAME, MACRO_MSG, MITE, NONCE, PRED,
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

declare_trace!($"nonce_fresh");

#[dynamic]
static FRESH_NONCE_PATTERN: Pattern<Lang> = {
    let ast = rexp!((FRESH_NONCE #0 #1 #2)).to_vec();
    RecExpr::from(ast).into()
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
            let nonce = {
                let SimplLang { head, args } = &egraph[nonce].nodes[0];
                Nonce {
                    name: head.clone(),
                    args: args.iter().map(|&id| convert_id(egraph, id)).collect(),
                }
            };

            let builder = RefFormulaBuilder::new(Mode::And, None);
            nonce.search_egraph(egraph, builder.clone(), content, Default::default());
            let search = builder.into_inner().unwrap().into_formula();

            conditions.push((hypothesis >> search).into_smt())
        }
        let condition = SmtFormula::Or(conditions);

        tr!("checking {condition}");
        let pbl: &mut Problem = egraph.analysis.pbl_mut();

        self.exec.run_to_dependancy(pbl, condition)
    }

    fn debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
        write!(f, "<fresh nonce>.")
    }
}

#[derive(Debug, Clone)]
pub struct Nonce {
    pub name: Function,
    pub args: Vec<RecFOFormula>,
}

fn convert_id<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> RecFOFormula {
    RecFOFormula::try_from_id(egraph, id).unwrap()
}

impl Nonce {
    pub fn into_recformula(self) -> RecFOFormula {
        let Self { name, args } = self;
        RecFOFormula::app(name, args)
    }

    pub fn search_egraph<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: RefFormulaBuilder,
        current: Id,
        visited: im_rc::HashSet<Id>,
    ) {
        tr!("looking at {current:}");
        ereturn_if!(builder.is_saturated());
        ereturn_if!(visited.contains(&current));
        tr!("unskipped");

        let eclass = &egraph[current];
        tr!(
            "current enode has {:} nodes\n({})",
            eclass.nodes.len(),
            pull_from_egraph(egraph, current).unwrap()
        );

        // first loop for early exit if necessary
        // This takes care of the cases that replace the whole builder
        for SimplLang { head, args } in eclass.iter() {
            tr!(
                "early looking through {head}:{current:}({})",
                args.iter().join(", ")
            );
            // check if I need to change mode (e.g., input)
            if head == &MACRO_FRAME
                && let Some((&time, &ptcl)) = args.iter().collect_tuple()
                && egraph[time].iter().any(|f| f.head == PRED)
            {
                tr!("looking through frame");
                tr!("builder mode {}", builder.borrow().mode());
                self.search_frame(egraph, &builder, time, ptcl);
                return;
            }

            // check is the nonce is there
            if head == &NONCE {
                tr!("found self ({})", self.name);
                let other = convert_id(egraph, current);
                builder.add_leaf(!EQ.rapp([other, NONCE.rapp([self.clone().into_recformula()])]));
                return; // <- no need to look further
            }
        }

        // main loop

        // fresh if indep of *one* of the e-class
        let builder = builder.add_node(Mode::Or, None);
        let visited = visited.update(current);

        for SimplLang { head, args } in eclass.iter() {
            tr!(
                "looking through {head}:{current:}({})",
                args.iter().join(", ")
            );
            // fresh if indep of all the *arguements*
            if head.is_special_subterm() {
                tr!("is special subterm (flags: {:?})", head.flags);
                // the special cases

                if head == &MITE || head == &BITE {
                    self.ite_egraph(egraph, &builder, args, visited.clone());
                }

                // The rest is taken care of by equality
            } else {
                for arg in args {
                    let builder = builder.add_node(Mode::And, Default::default());
                    self.search_egraph(egraph, builder.clone(), *arg, visited.clone());
                }
            }
        }
    }

    /// Builds the subterm of an if in the case of an eclass
    ///
    /// `visisted` must already be updated
    fn ite_egraph<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        args: &[Id],
        visited: im_rc::HashSet<Id>,
    ) {
        tr!("in ite");
        let builder = builder.add_node(Mode::And, Default::default());
        let (c, l, r) = args.iter().copied().collect_tuple().unwrap();

        self.search_egraph(egraph, builder.clone(), c, visited.clone());

        let c = convert_id(egraph, c);

        {
            // pos
            let cond = Condition {
                condition: c.clone(),
                variables: vec![],
                sorts: vec![],
                quantifier: FOBinder::Forall,
            };
            let builder = builder.add_node(Mode::Or, Some(cond));
            self.search_egraph(egraph, builder, l, visited.clone());
        }
        {
            // neg
            let cond = Condition {
                condition: !c,
                variables: vec![],
                sorts: vec![],
                quantifier: FOBinder::Forall,
            };
            let builder = builder.add_node(Mode::Or, Some(cond));
            self.search_egraph(egraph, builder, r, visited);
        }
    }

    fn search_frame<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        time: Id,
        ptcl: Id,
    ) {
        tr!("in frame");
        assert!(builder.current_mode().is_and());
        let time = convert_id(egraph, time);

        let pbl = egraph.analysis.pbl();

        // get the protocol from the function
        let ptcl = {
            let idx = egraph[ptcl]
                .iter()
                .find_map(|f| f.head.get_protocol_index())
                .unwrap(); // there has to be one
            &pbl.protocols()[idx]
        };

        // for each step we switch to `search_recexpr` on its message
        for Step {
            id,
            vars,
            cond,
            msg,
        } in ptcl.steps()
        {
            // build the condition object
            let condition = {
                let named = id.rapp(vars.iter().map(|v| RecFOFormula::Var(*v)));
                let happend_cond = HAPPENS.rapp([named.clone()]);
                let lt_cond = LT.rapp([named.clone(), time.clone()]);

                let condition = happend_cond & lt_cond;
                Condition {
                    condition,
                    variables: vars.clone(),
                    sorts: id.signature.inputs_iter().collect(),
                    quantifier: FOBinder::Forall,
                }
            };

            let builder = builder.add_node(Mode::And, Some(condition));
            self.inner_search_recexpr(pbl, &builder, cond);
            self.inner_search_recexpr(pbl, &builder, msg);
        }
    }
}

impl SyntaxSearcher for Nonce {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("nonce")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        fun == &NONCE
    }

    fn process_instance<'a>(
        &self,
        _: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(&'a [LangVar]),
    ) {
        assert_eq!(fun, NONCE);
        tr!("found nonce!");
        let arg = args.into_iter().next().expect("NONCE need a parameter");
        let content = !EQ.rapp([arg.into(), self.clone().into_recformula()]);
        builder.add_leaf(content);
    }
}

#[cfg(test)]
mod test {
    #[allow(unused_imports)]
    use cryptovampire_smt::{Smt, SmtFormula};
    #[allow(unused_imports)]
    use egg::{Analysis, EGraph, Id, Runner};
    #[allow(unused_imports)]
    use itertools::Itertools;

    use crate::{
        Lang, Problem, decl_fun, init_logger,
        problem::{PAnalysis, test::basic_hash::mk_pblm},
        rexp,
        rules::{
            base_rules::mk_rewrites_rules,
            nonce::Nonce,
            utils::fresh::{Mode, RefFormulaBuilder},
        },
        terms::{
            Function, HAPPENS, MACRO_COND, MACRO_INPUT, MACRO_MSG, RecFOFormula, Sort,
            formula_utils::convert_to_ground_rexp,
        },
    };

    fn mk_egraph<'a>(pbl: &'a mut Problem) -> (EGraph<Lang, PAnalysis<'a>>, Id, Id, Id) {
        let rw = mk_rewrites_rules(&pbl).collect_vec();

        let i = decl_fun!(pbl; "i": () -> Index);
        let j = decl_fun!(pbl; "j": () -> Index);
        let p1 = pbl.protocols()[0].name().clone();
        let tag = pbl.function.get("tag").unwrap();
        let rf = pbl.function.get("Rf").unwrap();

        let mut egraph = EGraph::new(PAnalysis::builder().pbl(pbl).build());
        let input_tag =
            egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_INPUT (tag i j) p1))).unwrap());
        let cond_rf =
            egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_COND (rf i) p1))).unwrap());
        let msg_tag =
            egraph.add_expr(&convert_to_ground_rexp(rexp!((MACRO_MSG (tag i j) p1))).unwrap());
        let ht = egraph.add_expr(&convert_to_ground_rexp(rexp!((HAPPENS (tag i j)))).unwrap());
        let hrf = egraph.add_expr(&convert_to_ground_rexp(rexp!((HAPPENS (rf i)))).unwrap());
        let mtrue = egraph.add_expr(&convert_to_ground_rexp(rexp!(true)).unwrap());
        egraph.union(ht, mtrue);
        egraph.union(hrf, mtrue);

        // egraph.rebuild();

        let runner: Runner<Lang, _> = Runner::new_with_egraph(egraph);
        let runner = runner.run(&rw);

        tr!("report: {}", runner.report());

        (runner.egraph, cond_rf, msg_tag, input_tag)
    }

    #[test]
    fn subterm_cond_rf() {
        init_logger();
        let mut pbl = mk_pblm().0;
        let (egraph, cond_rf, _, _) = mk_egraph(&mut pbl);
        let n = egraph.analysis.pbl().function.get("n").unwrap();
        let n = Nonce {
            name: n,
            args: vec![
                RecFOFormula::Var("?i".parse().unwrap()),
                RecFOFormula::Var("?j".parse().unwrap()),
            ],
        };

        let builder = RefFormulaBuilder::new(Mode::And, None);
        n.search_egraph(&egraph, builder.clone(), cond_rf, Default::default());

        let f = builder.into_inner().unwrap().into_formula();
        let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

        println!("formula: {smt}");
        panic!("wrong result")
    }

    #[test]
    fn subterm_msg_tag() {
        init_logger();
        let mut pbl = mk_pblm().0;
        let (egraph, _, _, msg_tag) = mk_egraph(&mut pbl);
        let pbl = egraph.analysis.pbl();
        let n = pbl.function.get("n").unwrap();
        let i = pbl.function.get("i").unwrap();
        let j = pbl.function.get("j").unwrap();
        let _ = pbl;
        let n = Nonce {
            name: n,
            args: vec![
                RecFOFormula::App {
                    head: i,
                    args: vec![],
                },
                RecFOFormula::App {
                    head: j,
                    args: vec![],
                },
            ],
        };

        let builder = RefFormulaBuilder::new(Mode::And, None);
        n.search_egraph(&egraph, builder.clone(), msg_tag, Default::default());

        let f = builder.into_inner().unwrap().into_formula();
        let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

        println!("formula: {smt}")
    }
}
