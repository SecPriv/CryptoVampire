use std::{
    borrow::{Borrow, Cow},
    cell::{Ref, RefCell},
    collections::HashMap,
    fmt::{Debug, Write},
    ops::{Deref, DerefMut},
    rc::Rc,
};

use bon::Builder;
use cryptovampire_macros::smt;
use cryptovampire_smt::{Smt, SortedVar};
use egg::{Analysis, EGraph, RecExpr};
use golgge::{Program, PrologRule, Rule, WeightedAnalysis};
use itertools::{Itertools, chain};
use logic_formula::egg::SimpleDiscriminant;
use serde::Serialize;
use utils::ereturn_let;

use crate::{
    Configuration, Lang, LangVar, MSmt, mk_signature,
    protocol::Protocol,
    rexp,
    rules::{
        FreshNonce, VampireRule,
        base_rules::{mk_equiv_rules, mk_rewrites_rules},
    },
    terms::{
        EMPTY, EQUIV, Function, FunctionCollection, FunctionFlags, HAPPENS, InnerFunction,
        MACRO_FRAME, PRED, Rewrite, TRUE, UNFOLD_MSG, formula_utils::convert_to_ground_rexp,
    },
    vampire::{mk_prelude, runner::VampireExec},
};

mod analysis;
pub use analysis::{PAnalysis, PRule, RcRule};

declare_trace!($"problem");

/// A problem for the solver to solve
#[derive(Builder)]
pub struct Problem {
    /// The configuration (e.g., cli arguments and such)
    #[builder(default)]
    pub config: Configuration,
    /// The protocol we want to prove indistiguishability on
    ///
    /// The vector must be at least 2 long
    #[builder(with = <_>::from_iter, default = vec![])]
    pub protocols: Vec<Protocol>,
    /// The functions
    #[builder(default = FunctionCollection::init())]
    pub function: FunctionCollection,

    #[builder(with = <_>::from_iter, default = vec![])]
    extra_rules: Vec<RcRule>,
    #[builder(with = <_>::from_iter, default = vec![])]
    extra_rewrite: Vec<Rewrite>,
    #[builder(with = <_>::from_iter, default = vec![])]
    extra_smt: Vec<MSmt>,

    #[builder(skip)]
    smt_prelude: Option<Vec<MSmt>>,
}

impl Default for Problem {
    fn default() -> Self {
        Self {
            config: Default::default(),
            protocols: vec![],
            function: FunctionCollection::init(),
            extra_rules: vec![],
            extra_rewrite: vec![],
            extra_smt: vec![],
            smt_prelude: None,
        }
    }
}

impl Problem {
    pub fn base_empty() -> Self {
        Self::default()
    }

    pub fn valid(&self) -> bool {
        self.protocols
            .iter()
            .tuple_windows()
            .all(|(a, b)| Protocol::are_compatible(a, b))
    }

    /// Simply declare a protocol, this one remains quite undefined
    pub fn declare_new_protocol(&mut self) -> &mut Protocol {
        self.clear_smt_prelude();
        let n = self.protocols.len();

        let inner = InnerFunction {
            flags: FunctionFlags::PROTOCOL,
            protocol_idx: n,
            ..InnerFunction::new(format!("_p${n:}").into(), mk_signature!(() -> Protocol))
        };
        let fun = Function::new(inner);
        self.function.add(fun.clone());

        let ptcl = Protocol::new(fun);
        self.protocols.push(ptcl);
        &mut self.protocols[n]
    }

    pub fn get_init_fun(&self) -> &Function {
        &self.protocols[0].steps()[0].id
    }

    /// Build a [Program] to use
    pub fn mk_program<'a>(&'a mut self) -> Program<Lang, PAnalysis<'a>> {
        let exec = Rc::new(
            VampireExec::builder()
                .keep_file(self.config.keep_smt_files)
                .build(),
        );
        let vampire_rule = VampireRule::builder().exec(exec.clone()).build();
        let fresh_rule = FreshNonce::builder().exec(exec.clone()).build();

        let eq_rules = mk_rewrites_rules(self);
        let rules = mk_equiv_rules(self).map(Rule::into_rc);
        golgge::Program::build()
            .eq_rules(eq_rules)
            .rules(chain![
                rules,
                [vampire_rule.into_rc(), fresh_rule.into_rc()]
            ])
            .egraph(EGraph::new(PAnalysis::builder().pbl(self).build()))
            .call()
    }

    pub fn run(&mut self, p1: usize, p2: usize) -> bool {
        assert!(
            p1 < self.protocols.len(),
            "p1 in not a protocol of `self` (index to large"
        );
        assert!(
            p2 < self.protocols.len(),
            "p2 in not a protocol of `self` (index to large"
        );
        debug_assert!(self.valid());

        let depth = self.config.depth;
        let base_smt_n = self.extra_smt().len();

        let p1f = self.protocols[p1].name().clone();
        let p2f = self.protocols[p2].name().clone();

        let mut res = true;

        {
            tr!("running input step");
            assert_eq!(
                self.protocols[p1].steps()[0].id.name,
                "init",
                "the first step isn't an `init` (in p1)"
            );
            assert_eq!(
                self.protocols[p2].steps()[0].id.name,
                "init",
                "the first step isn't an `init` (in p2)"
            );

            let init = self.get_init_fun().clone();

            // we add to `extra_smt` things specific to this run that need to be reflected in smt
            self.extra_smt_mut()
                .push(Smt::mk_assert(smt!((HAPPENS init))));

            let mut pgrm = self.mk_program();

            {
                // same but for the egraph
                let egraph = pgrm.egraph_mut();
                let id_true = egraph.add_expr(&TRUE.app_empty());
                let id_h = egraph.add_expr(&HAPPENS.app(&[init.app_empty()]));
                egraph.union(id_true, id_h);
            }

            res &= pgrm.run_expr(
                convert_to_ground_rexp(
                    rexp!((EQUIV EMPTY EMPTY (UNFOLD_MSG init p1f) (UNFOLD_MSG init p2f))),
                )
                .unwrap(),
                depth,
            );
        }

        // just to make things cleaner
        let get_steps = |i: usize| {
            self.protocols[i]
                .steps()
                .iter()
                .map(|s| s.id.clone())
                .collect_vec()
        };

        let steps = get_steps(p1);
        assert!(steps == get_steps(p2));

        for s in &steps[1..] {
            if !res {
                // early exists if we failed to prive one result
                tr!("false!");
                return res;
            }

            tr!("running step {}", s.name);

            // we ensure we remove the extra stuff from the previous run
            self.extra_smt_mut().truncate(base_smt_n);

            // add and collect functions that will serve as ground indices for the search
            let args = s
                .signature
                .inputs
                .iter()
                .enumerate()
                .map(|(i, &sort)| {
                    self.function
                        .add_function()
                        .output(sort)
                        .name(format!("{}_{i:}", s.name))
                        .call()
                })
                .collect_vec();

            self.extra_smt.push(Smt::mk_assert({
                let args = args.iter().map(|f| smt!(f));
                smt!((HAPPENS (s #args*)))
            }));

            // The macros are not helpful here unfortunately...
            let args: Vec<RecExpr<Lang>> = args.into_iter().map(|f| f.app_empty()).collect_vec();
            let s = s.app(&args);
            let goal = {
                let pred_s = PRED.app(std::slice::from_ref(&s));
                let p1f = p1f.app_empty();
                let p2f = p2f.app_empty();

                EQUIV.app(&[
                    MACRO_FRAME.app(&[pred_s.clone(), p1f.clone()]),
                    MACRO_FRAME.app(&[pred_s.clone(), p2f.clone()]),
                    MACRO_FRAME.app(&[s.clone(), p1f.clone()]),
                    MACRO_FRAME.app(&[s.clone(), p2f.clone()]),
                ])
            };

            let mut pgrm = self.mk_program();

            {
                let egraph = pgrm.egraph_mut();
                let id_true = egraph.add_expr(&TRUE.app_empty());
                let id_h = egraph.add_expr(&HAPPENS.app(std::slice::from_ref(&s)));
                egraph.union(id_true, id_h);
            }

            res &= pgrm.run_expr(goal, depth);
        }

        self.extra_smt_mut().truncate(base_smt_n);

        res
    }

    fn compute_smt_prelude(&mut self) {
        if self.smt_prelude.is_none() {
            let prelude = mk_prelude(self).collect();
            self.smt_prelude = Some(prelude)
        }
    }

    pub fn get_smt_prelude(&mut self) -> &[MSmt] {
        self.compute_smt_prelude();
        self.smt_prelude.as_ref().unwrap()
    }

    pub fn clear_smt_prelude(&mut self) {
        self.smt_prelude = None;
    }

    pub fn extra_smt(&self) -> &[MSmt] {
        &self.extra_smt
    }

    pub fn extra_smt_mut(&mut self) -> &mut Vec<MSmt> {
        self.clear_smt_prelude();
        &mut self.extra_smt
    }

    pub fn extra_rewrite(&self) -> &[Rewrite] {
        &self.extra_rewrite
    }

    pub fn extra_rewrite_mut(&mut self) -> &mut Vec<Rewrite> {
        self.clear_smt_prelude();
        &mut self.extra_rewrite
    }

    pub fn extra_rules(&self) -> &[RcRule] {
        &self.extra_rules
    }

    pub fn extra_rules_mut(&mut self) -> &mut Vec<RcRule> {
        &mut self.extra_rules
    }
}

impl Debug for Problem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Problem")
            .field("config", &self.config)
            .field("protocols", &self.protocols)
            .field("function", &self.function)
            .field(
                "extra_rules",
                &self
                    .extra_rules
                    .iter()
                    .map(|x| golgge::DebugRule::new(x.as_ref()))
                    .collect_vec(),
            )
            .field("extra_rewrite", &self.extra_rewrite)
            .field("extra_smt", &self.extra_smt)
            .finish()
    }
}

impl AsRef<FunctionCollection> for Problem {
    fn as_ref(&self) -> &FunctionCollection {
        &self.function
    }
}

impl AsMut<FunctionCollection> for Problem {
    fn as_mut(&mut self) -> &mut FunctionCollection {
        &mut self.function
    }
}

#[cfg(test)]
pub mod test;
