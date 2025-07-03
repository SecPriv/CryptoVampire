//! Nonce freshness

use std::rc::Rc;

use crate::problem::PAnalysis;
use crate::protocol::Step;
use crate::rules::fresh::{Condition, Mode};
use crate::terms::formula_utils::{offsets_owned, pull_from_egraph};
use crate::terms::{
    Alias, AliasRewrite, BITE, EQ, Exists, FOBinder, FRESH_NONCE, HAPPENS, LT, MACRO_COND,
    MACRO_FRAME, MACRO_MSG, MITE, NONCE, PRED,
};
use crate::vampire::runner::VampireExec;
use crate::{
    Lang,
    rules::fresh::RefFormulaBuilder,
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

        {
            let prelude = pbl.get_smt_prelude();
            // let pbl: &Problem<_> = &self.pbl.borrow();
            let res = self
                .exec
                .run_smt(chain![
                    prelude.iter().cloned(),
                    [Smt::mk_query(condition), Smt::CheckSat]
                ])
                .expect("something went wrong with vampire");

            if res {
                Dependancy::axiom()
            } else {
                Dependancy::impossible()
            }
        }
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
                tr!("builder mode {}", builder.borrow().mode);
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
            self.search_recexpr(pbl, &builder, cond);
            self.search_recexpr(pbl, &builder, msg);
        }
    }

    pub fn search_recexpr(&self, pbl: &Problem, builder: &RefFormulaBuilder, term: &[LangVar]) {
        assert!(builder.current_mode().is_and());
        ereturn_if!(builder.is_saturated());
        ereturn_let!(let Destructed { head: HeadSk::Fun(fun), mut args} = term.destruct());
        tr!(
            "searching thourgh {}",
            egg::RecExpr::from(term.iter().cloned().collect_vec())
        );

        if fun == NONCE {
            tr!("found nonce!");
            let arg = args.next().expect("NONCE need a parameter");
            let content = !EQ.rapp([arg.into(), self.clone().into_recformula()]);
            builder.add_leaf(content);
        } else if fun.is_special_subterm() {
            self.search_special_recexpr(pbl, builder, fun, args);
        } else {
            // base case
            for arg in args {
                self.search_recexpr(pbl, builder, arg);
            }
        }
    }

    fn search_special_recexpr<'a>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(&'a [LangVar]),
    ) {
        assert!(builder.current_mode().is_and());
        assert!(fun.is_special_subterm());
        tr!("in search_special_recexpr");

        if fun == MACRO_COND || fun == MACRO_MSG {
            todo!()
        } else if let Some(alias) = fun.get_alias() {
            self.search_alias(pbl, builder, alias, args);
        } else if let Some(exists) = fun.get_exists(&pbl.function) {
            self.search_exists(pbl, builder, exists, args);
        }
    }

    fn search_alias<'a>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        Alias(rws): &Alias,
        args: implvec!(&'a [LangVar]),
    ) {
        assert!(builder.current_mode().is_and());
        tr!("in search_alias");
        let args = args.into_iter().collect_vec();
        let max_var = args
            .iter()
            .flat_map(|arg| arg.used_vars_iter())
            .filter_map(|v| v.expose().try_into_num().ok())
            .max()
            .unwrap_or(0)
            + 1;
        tr!("max_var = {max_var}");

        let builder = builder.add_node(Mode::Or, None);

        for AliasRewrite {
            from,
            to,
            variables,
            sorts,
        } in rws.iter()
        {
            assert!(
                variables
                    .iter()
                    .all(|v| matches!(v.expose(), VarExposed::Num(_))),
                "only numeric variables are allowed in aliases"
            );

            let variables = variables
                .iter()
                .map(|v| match v.expose() {
                    VarExposed::Num(i) => (i + max_var).into(),
                    VarExposed::Sym(_) => *v,
                })
                .collect_vec();
            let from = from
                .iter()
                .map(|f| offsets_owned(max_var, f.iter().cloned()))
                .collect_vec();
            let to = offsets_owned(max_var, to.iter().cloned());

            let condition = RecFOFormula::and(
                izip!(args.iter(), from.iter())
                    .map(|(arg, f)| EQ.rapp(vec![RecFOFormula::from(*arg), f.as_ref().into()])),
            );
            let condition = Condition {
                condition,
                variables: variables.to_vec(),
                sorts: sorts.to_vec(),
                quantifier: FOBinder::Exists,
            };
            let builder = builder.add_node(Mode::And, Some(condition));
            self.search_recexpr(pbl, &builder, &to);
            for arg in &args {
                self.search_recexpr(pbl, &builder, arg);
            }
        }
    }

    fn search_exists<'a>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        e @ Exists {
            vars,
            bound_var,
            patt,
            ..
        }: &Exists,
        args: implvec!(&'a [LangVar]),
    ) {
        tr!("in search_exists {e}");
        let sort = e.get_var_sort();

        // capture avoiding substitution. We need to rename the bound variable of the exists in case it clashes
        let nvar;
        let content = {
            let mut subst = izip!(
                vars.iter().cloned(),
                args.into_iter().map(Vec::from).map(RecExpr::from)
            )
            .collect_vec();
            let max_var = subst
                .iter()
                .flat_map(|(_, x)| x.free_vars_iter())
                .filter_map(|v| match v.expose() {
                    egg::VarExposed::Num(n) => Some(n),
                    _ => None,
                })
                .max()
                .unwrap_or(0);
            nvar = Var::from_u32(max_var);
            subst.push((*bound_var, vec![ENodeOrVar::Var(nvar)].into()));

            patt.clone().apply_pattern_subst(subst)
        };

        let condition = Condition {
            condition: RecFOFormula::True(),
            variables: vec![nvar],
            sorts: vec![sort],
            quantifier: FOBinder::Forall,
        };
        let builder = builder.add_node(Mode::And, Some(condition));
        self.search_recexpr(pbl, &builder, &content);
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
            fresh::{Mode, RefFormulaBuilder, nonce::Nonce},
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
