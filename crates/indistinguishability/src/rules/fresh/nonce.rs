//! Nonce freshness

use egg::{Analysis, EGraph, Id};
use egg::{ENodeOrVar, Language, RecExpr, Var};
use itertools::{Itertools, izip};
use log::trace;
use logic_formula::egg::SimplLang;
use logic_formula::{Destructed, Formula, HeadSk};
use utils::traits::Named;
use utils::{econtinue_if, ereturn_if, ereturn_let, implvec, match_eq};

use crate::protocol::Step;
use crate::rules::fresh::{Condition, Mode};
use crate::terms::{
    Alias, AliasRewrite, BITE, EQ, Exists, FOBinder, HAPPENS, LEQ, LT, MACRO_COND, MACRO_FRAME,
    MACRO_MSG, MITE, NOT, PRED, UNFOLD_FRAME, flags,
};
use crate::{
    Lang,
    rules::fresh::RefFormulaBuilder,
    terms::{Function, MACRO_INPUT, RecFOFormula},
};
use crate::{LangVar, Problem};

#[derive(Debug, Clone)]
pub struct Nonce {
    pub name: Function,
    pub args: Vec<RecFOFormula>,
}

fn convert_id<N: Analysis<Lang>>(egraph: &EGraph<Lang, N>, id: Id) -> RecFOFormula {
    let other = egraph
        .id_to_expr(id)
        .into_iter()
        .map(egg::ENodeOrVar::ENode)
        .collect_vec();
    RecFOFormula::from(other.as_slice())
}

impl Nonce {
    pub fn into_recformula(self) -> RecFOFormula {
        let Self { name, args } = self;
        RecFOFormula::app(name, args)
    }

    pub fn search_egraph<N: Analysis<Lang>>(
        &self,
        pbl: &Problem,
        egraph: &EGraph<Lang, N>,
        builder: RefFormulaBuilder,
        current: Id,
        visited: im_rc::HashSet<Id>,
    ) {
        trace!("looking at {current:}");
        ereturn_if!(builder.is_saturated());
        ereturn_if!(visited.contains(&current));
        trace!("unskipped");

        let eclass = &egraph[current];
        trace!(
            "current enode has {:} nodes\n({})",
            eclass.nodes.len(),
            egraph.id_to_expr(current)
        );

        // first loop for early exit if necessary
        // This takes care of the cases that replace the whole builder
        for SimplLang { head, args } in eclass.iter() {
            trace!(
                "early looking through {head}:{current:}({})",
                args.iter().join(", ")
            );
            // check if I need to change mode (e.g., input)
            if head == &MACRO_FRAME
                && let Some((&time, &ptcl)) = args.iter().collect_tuple()
                && egraph[time].iter().any(|f| f.head == PRED)
            {
                trace!("looking through frame");
                self.search_frame(pbl, egraph, &builder, time, ptcl);
                return;
            }

            // check is the nonce is there
            if head == &self.name {
                trace!("found self ({})", self.name);
                let other = convert_id(egraph, current);
                builder.add_leaf(!EQ.rapp([other, self.clone().into_recformula()]));
                return; // <- no need to look further
            }
        }

        // main loop

        // fresh if indep of *one* of the e-class
        let builder = builder.add_node(Mode::Or, None);
        let visited = visited.update(current);

        for SimplLang { head, args } in eclass.iter() {
            trace!(
                "looking through {head}:{current:}({})",
                args.iter().join(", ")
            );
            // fresh if indep of all the *arguements*
            if head.is_special_subterm() {
                trace!("is special subterm (flags: {:?})", head.flags);
                // the special cases

                if head == &MITE || head == &BITE {
                    self.ite_egraph(pbl, egraph, &builder, args, visited.clone());
                }

                // The rest is taken care of by equality
            } else {
                for arg in args {
                    let builder = builder.add_node(Mode::And, Default::default());
                    self.search_egraph(pbl, egraph, builder.clone(), *arg, visited.clone());
                }
            }
        }
    }

    /// Builds the subterm of an if in the case of an eclass
    ///
    /// `visisted` must already be updated
    fn ite_egraph<N: Analysis<Lang>>(
        &self,
        pbl: &Problem,
        egraph: &EGraph<Lang, N>,
        builder: &RefFormulaBuilder,
        args: &[Id],
        visited: im_rc::HashSet<Id>,
    ) {
        trace!("in ite");
        let builder = builder.add_node(Mode::And, Default::default());
        let (c, l, r) = args.iter().copied().collect_tuple().unwrap();

        self.search_egraph(pbl, egraph, builder.clone(), c, visited.clone());

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
            self.search_egraph(pbl, egraph, builder, l, visited.clone());
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
            self.search_egraph(pbl, egraph, builder, r, visited);
        }
    }

    fn search_frame<N: Analysis<Lang>>(
        &self,
        pbl: &Problem,
        egraph: &EGraph<Lang, N>,
        builder: &RefFormulaBuilder,
        time: Id,
        ptcl: Id,
    ) {
        trace!("in frame");
        assert!(builder.current_mode().is_and());
        let time = convert_id(egraph, time);

        // get the protocol from the function
        let ptcl = {
            let idx = egraph[ptcl]
                .iter()
                .find_map(|f| f.head.get_protocol_index())
                .unwrap(); // there has to be one
            &pbl.protocols[idx]
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
        ereturn_let!(let Destructed { head: HeadSk::Fun(fun), args} = term.destruct());
        trace!(
            "searching thourgh {}",
            egg::RecExpr::from(term.iter().cloned().collect_vec())
        );

        if fun == self.name {
            let content = !EQ.rapp([term.into(), self.clone().into_recformula()]);
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
        trace!("in search_special_recexpr");

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
        trace!("in search_alias");
        let args = args.into_iter().collect_vec();

        let builder = builder.add_node(Mode::Or, None);

        for AliasRewrite {
            from,
            to,
            variables,
            sorts,
        } in rws.iter()
        {
            let condition = RecFOFormula::and(
                izip!(args.iter(), from.iter())
                    .map(|(arg, f)| EQ.rapp(vec![RecFOFormula::from(*arg), f.as_ref().into()])),
            );
            let condition = Condition {
                condition,
                variables: variables.to_vec(),
                sorts: sorts.to_vec(),
                // unless the alias is malformed, this should just be unification. Hence the forall
                quantifier: FOBinder::Forall,
            };
            let builder = builder.add_node(Mode::And, Some(condition));
            self.search_recexpr(pbl, &builder, to);
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
        trace!("in search_exists");
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
    use cryptovampire_smt::{Smt, SmtFormula};
    use egg::{EGraph, Id, Runner};
    use itertools::Itertools;
    use log::trace;

    use crate::{
        Lang, Problem, decl_fun, init_logger,
        problem::test::basic_hash::mk_pblm,
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

    fn mk_egraph() -> (Problem, EGraph<Lang, ()>, Id, Id, Id) {
        let mut pbl = mk_pblm();
        let i = decl_fun!(&mut pbl; "i": () -> Index);
        let j = decl_fun!(&mut pbl; "j": () -> Index);
        let p1 = pbl.protocols[0].name();
        let tag = pbl.function.get("tag").unwrap();
        let rf = pbl.function.get("Rf").unwrap();

        let mut egraph = EGraph::new(());
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

        let rw = mk_rewrites_rules(&pbl).collect_vec();
        let runner: Runner<Lang, ()> = Runner::new(());
        let runner = runner.with_egraph(egraph).run(&rw);

        trace!("report: {}", runner.report());

        (pbl, runner.egraph, cond_rf, msg_tag, input_tag)
    }

    #[test]
    fn subterm_cond_rf() {
        init_logger();
        let (mut pbl, egraph, cond_rf, _, _) = mk_egraph();
        let n = pbl.function.get("n").unwrap();
        let i = decl_fun!(&mut pbl; "i2": () -> Index);
        let n = Nonce {
            name: n,
            args: vec![
                RecFOFormula::Var("?i".parse().unwrap()),
                RecFOFormula::Var("?j".parse().unwrap()),
            ],
        };

        let builder = RefFormulaBuilder::new(Mode::And, None);
        n.search_egraph(&pbl, &egraph, builder.clone(), cond_rf, Default::default());

        let f = builder.into_inner().unwrap().into_formula();
        let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

        println!("formula: {smt}");
        panic!("wrong result")
    }

    #[test]
    fn subterm_msg_tag() {
        init_logger();
        let (mut pbl, egraph, _, _, msg_tag) = mk_egraph();
        let n = pbl.function.get("n").unwrap();
        let i = pbl.function.get("i").unwrap();
        let j = pbl.function.get("j").unwrap();
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
        n.search_egraph(&pbl, &egraph, builder.clone(), msg_tag, Default::default());

        let f = builder.into_inner().unwrap().into_formula();
        let smt: SmtFormula<Sort, Function> = SmtFormula::from_formula(f);

        println!("formula: {smt}")
    }
}
