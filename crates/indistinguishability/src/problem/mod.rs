use std::borrow::Cow;
use std::fmt::Debug;
use std::num::NonZeroUsize;
use std::rc::Rc;

use bon::bon;
use cryptovampire_smt::Smt;
use egg::{EGraph, RecExpr};
use golgge::{Program, Rule};
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::Formula;
use logic_formula::iterators::QuantiferIterator;
use utils::{econtinue_let, implvec};

use crate::problem::function_builder::{
    SetAlias, SetCryptography, SetInputs, SetName, SetOutput, SetStepIdx,
};
use crate::protocol::{Protocol, Step};
use crate::rules::{FreshNonce, VampireRule, mk_default_prolog_rules, mk_default_rewrites};
use crate::runners::SmtRunner;
use crate::smt::mk_prelude;
use crate::terms::{
    Alias, CryptographicAssumption, EMPTY, EQUIV, FOBinder, FindSuchThat, Function,
    FunctionCollection, FunctionFlags, HAPPENS, INIT, InnerFunction, MACRO_FRAME, PRED,
    QuantifierT, QuantifierTranslator, RecFOFormula, Rewrite, Signature, Sort, TRUE, UNFOLD_MSG,
};
use crate::utils::fresh_name;
use crate::{Configuration, Lang, MSmt, mk_signature, rexp, smt};

mod analysis;
pub use analysis::{PAnalysis, PRule, RcRule};

declare_trace!($"problem");

/// A problem for the solver to solve
#[non_exhaustive]
pub struct Problem {
    /// The configuration (e.g., cli arguments and such)
    pub config: Configuration,
    /// The protocol we want to prove indistiguishability on
    ///
    /// The vector must be at least 2 long
    protocols: Vec<Protocol>,
    /// The functions
    function: FunctionCollection,

    cryptography: Vec<CryptographicAssumption>,

    extra_rules: Vec<RcRule>,
    extra_rewrite: Vec<Rewrite>,
    extra_smt: Vec<MSmt>,

    /// cache for the smt prelude
    smt_prelude: Option<Vec<MSmt>>,

    /// the current step in the run (if any)
    current_step: Option<CurrentStep>,

    quantifier_cache: Vec<(RecFOFormula, Function)>,
}

impl Default for Problem {
    fn default() -> Self {
        Self::builder().build()
    }
}

impl Problem {
    pub fn valid(&self) -> bool {
        self.protocols
            .iter()
            .tuple_windows()
            .all(|(a, b)| Protocol::are_compatible(a, b))
    }

    pub fn get_init_fun(&self) -> &Function {
        &INIT
    }

    /// Build a [Program] to use
    pub fn mk_program<'a>(&'a mut self) -> Program<Lang, PAnalysis<'a>> {
        let exec = SmtRunner::new(&self);
        let vampire_rule = VampireRule::builder().exec(exec.clone()).build();
        let fresh_rule = FreshNonce::builder().exec(exec.clone()).build();

        let eq_rules = mk_default_rewrites(self);
        let rules = mk_default_prolog_rules(self);
        let rules: Vec<Rc<dyn Rule<_, _>>> =
            chain![rules, [vampire_rule.into_mrc(), fresh_rule.into_mrc()]].collect_vec();

        golgge::Program::build()
            .eq_rules(eq_rules)
            .rules(rules)
            .egraph(EGraph::new(PAnalysis::builder().pbl(self).build()).with_explanations_enabled())
            .config(golgge::Config::builder().node_limit(500).build())
            .call()
    }

    pub fn run(&mut self, p1: usize, p2: usize) -> bool {
        assert!(
            p1 < self.protocols.len(),
            "p1 in not a protocol of `self` (index to large)"
        );
        assert!(
            p2 < self.protocols.len(),
            "p2 in not a protocol of `self` (index to large)"
        );
        debug_assert!(self.valid());

        let depth = self.config.depth;
        let base_smt_n = self.extra_smt().len();

        let p1f = self.protocols[p1].name().clone();
        let p2f = self.protocols[p2].name().clone();

        // the result of the computation
        let mut res = true;

        // the steps in the problem
        let mut steps = {
            // just to make things cleaner
            let get_steps = |i: usize| {
                self.protocols[i]
                    .steps()
                    .iter()
                    .map(|s| s.id.clone())
                    .collect_vec()
            };

            let steps = get_steps(p1);
            assert!(
                steps == get_steps(p2),
                "not the same steps in both protocols!"
            );
            steps.into_iter().enumerate()
        };

        if let Some((idx, init)) = steps.next() {
            debug_assert_eq!(idx, 0);
            self.current_step = Some(CurrentStep { idx, args: vec![] });

            tr!("running input step");
            assert_eq!(init.name, "init");

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

            res &= pgrm
                .run_expr(
                    rexp!((EQUIV EMPTY EMPTY (UNFOLD_MSG init p1f) (UNFOLD_MSG init p2f)))
                        .as_egg_ground(),
                    depth,
                )
                .as_bool();
        } else {
            trace!("empty problem");
            return true;
        }

        for (idx, s) in steps {
            self.current_step = None;

            if !res {
                // early exists if we failed to prove one result
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
                    self.declare_function()
                        .output(sort)
                        .name(format!("{}_{i:}", s.name))
                        .call()
                })
                .collect_vec();

            self.current_step = Some(CurrentStep {
                idx,
                args: args.clone(),
            });

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

            res &= pgrm.run_expr(goal, depth).as_bool();
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

    pub fn protocols(&self) -> &[Protocol] {
        &self.protocols
    }

    pub fn protocol_mut(&mut self, index: usize) -> Option<&mut Protocol> {
        self.protocols.get_mut(index)
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

        let ptcl = {
            let builder = Protocol::builder().name(fun);
            if let Some(p0) = self.protocols().first() {
                builder
                    .steps(p0.steps().iter().map(|Step { id, vars, .. }| {
                        Step::builder()
                            .id(id.clone())
                            .vars(vars.clone())
                            .build()
                            .unwrap()
                    }))
                    .build()
            } else {
                builder.build()
            }
        };
        self.protocols.push(ptcl);
        &mut self.protocols[n]
    }

    /// Push steps to all protocols, returns a mutable pointer to those steps
    ///
    /// The ith steps is pushed to the ith protocol
    ///
    /// ### panic
    /// If the number if steps is different from the number of protocol or they use different [Function]
    pub fn push_steps(&mut self, steps: implvec!(Step)) -> Vec<&mut Step> {
        let steps = steps
            .into_iter()
            .zip_eq(&mut self.protocols)
            .map(|(s, p)| p.add_step(s))
            .collect_vec();
        assert!(
            steps.iter().map(|s| &s.id).all_equal(),
            "The steps should all have the same name"
        );
        steps
    }

    pub fn steps(&self) -> Option<impl Iterator<Item = Function> + use<'_>> {
        Some(
            self.protocols()
                .first()?
                .steps()
                .iter()
                .map(|Step { id, .. }| id.clone()),
        )
    }

    pub fn num_steps(&self) -> Option<NonZeroUsize> {
        let n = self.protocols().first()?.steps().len();
        let n = NonZeroUsize::new(n)
            .expect("a protocol has no steps, a protocol should always at least have an INIT step");
        Some(n)
    }

    /// returns the [Function] associated to the `index`th [Step] if it exists
    pub fn get_step_name(&self, index: usize) -> Option<&Function> {
        self.protocols().first()?.steps().get(index).map(|s| &s.id)
    }

    pub fn num_protocols(&self) -> usize {
        self.protocols().len()
    }

    pub fn cryptography(&self) -> &[CryptographicAssumption] {
        &self.cryptography
    }

    pub fn cryptography_mut(&mut self, index: usize) -> Option<&mut CryptographicAssumption> {
        self.cryptography.get_mut(index)
    }

    pub fn extend_cryptography<const N: usize>(&mut self) -> [usize; N] {
        let ret = std::array::from_fn(|i| i + self.cryptography.len());
        self.cryptography.extend(ret.map(|_| Default::default()));
        ret
    }

    #[allow(dead_code)]
    pub(crate) fn current_step(&self) -> Option<&CurrentStep> {
        self.current_step.as_ref()
    }

    pub fn functions(&self) -> &FunctionCollection {
        &self.function
    }

    pub fn functions_mut(&mut self) -> &mut FunctionCollection {
        self.clear_smt_prelude();
        &mut self.function
    }

    pub fn find_temp_quantifiers(&mut self, extra: &[RecFOFormula]) {
        // unique quantifiers up to unification
        let quantifiers = {
            let candidate = chain![self.list_all_terms(), extra]
                .flat_map(|f| f.iter_with(QuantiferIterator, ()))
                .unique();
            let mut pile = Vec::new();
            for a in candidate {
                if let RecFOFormula::Quantifier {
                    head: FOBinder::FindSuchThat,
                    ..
                } = a
                    && let None = pile.iter().find_map(|x| a.unify(x))
                    && let None = self.quantifier_cache.iter().find_map(|(x, _)| a.unify(x))
                {
                    pile.push(a.clone());
                }
            }
            pile
        };

        if quantifiers.is_empty() {
            return;
        }

        for q in quantifiers.iter() {
            econtinue_let!(let RecFOFormula::Quantifier { vars, arg, .. } = q);
            let cvars_sorts = q.free_vars_iter().map(|v| {
                v.get_sort()
                    .expect("quantifiers should capture variables with sort")
            });
            let bvars_sorts = vars.iter().map(|v| {
                v.get_sort()
                    .expect("quantified variables should have a sort")
            });
            let find = FindSuchThat::insert()
                .pbl(self)
                .bvars_sorts(bvars_sorts)
                .cvars_sorts(cvars_sorts)
                .temporary(true)
                .call();
            find.set_condition(arg[0].clone());
            find.set_then_branch(arg[1].clone());
            find.set_else_branch(arg[2].clone());
            let tlf = find.top_level_function().clone();
            self.quantifier_cache.push((q.clone(), tlf));
        }
        self.clear_smt_prelude();
    }

    pub fn clear_temp_quantifiers(&mut self) {
        self.quantifier_cache.clear();
        self.clear_smt_prelude();
    }

    /// list all the `RecFOFormula` stored in this `Self`
    pub fn list_all_terms(&self) -> impl Iterator<Item = &RecFOFormula> {
        self.protocols()
            .iter()
            .flat_map(|p| p.steps().iter())
            .flat_map(|s| [&s.cond, &s.msg].into_iter())
    }
}

impl QuantifierTranslator for Problem {
    fn try_translate(&self, formula: &RecFOFormula) -> Option<crate::terms::RecFOFormula> {
        let (subst, fun) = self
            .quantifier_cache
            .iter()
            .find_map(|(cached, fun)| cached.unify(formula).map(|subst| (subst, fun.clone())))?;
        let q = fun.get_quantifier(self.functions()).unwrap();

        let args: Option<Vec<_>> = q.cvars().iter().map(|v| subst.get(v)).collect();
        let args = args?;
        let args = args.iter().cloned().cloned();

        let sks = q.skolems().iter().map(|sk| rexp!((sk #(args.clone())*)));
        let tlf = q.top_level_function();

        Some(rexp!((tlf #(args.clone())* #sks*)))
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

#[bon]
impl Problem {
    fn default_cryptography() -> Vec<CryptographicAssumption> {
        vec![CryptographicAssumption::NoGuessingTh]
    }

    #[builder(builder_type = ProblemBuilder)]
    pub fn new(
        #[builder(field = Self::default_cryptography())] cryptography: Vec<CryptographicAssumption>,
        #[builder(field = None)] smt_prelude: Option<Vec<MSmt>>,
        /// The configuration (e.g., cli arguments and such)
        #[builder(default)]
        config: Configuration,
        /// The protocol we want to prove indistiguishability on
        ///
        /// The vector must be at least 2 long
        #[builder(with = <_>::from_iter, default = vec![])]
        protocols: Vec<Protocol>,
        /// The functions
        #[builder(default = FunctionCollection::init())]
        function: FunctionCollection,

        #[builder(with = <_>::from_iter, default = vec![])] extra_rules: Vec<RcRule>,
        #[builder(with = <_>::from_iter, default = vec![])] extra_rewrite: Vec<Rewrite>,
        #[builder(with = <_>::from_iter, default = vec![])] extra_smt: Vec<MSmt>,
    ) -> Self {
        Self {
            config,
            protocols,
            function,
            cryptography,
            extra_rules,
            extra_rewrite,
            extra_smt,
            smt_prelude,
            current_step: None,
            quantifier_cache: vec![],
        }
    }

    #[builder(builder_type = FunctionBuilder)]
    pub fn declare_function(
        &mut self,
        #[builder(field)] flags: FunctionFlags,
        #[builder(into)] name: Cow<'static, str>,
        #[builder(with = FromIterator::from_iter, default = vec![])] inputs: Vec<Sort>,
        output: Sort,
        alias: Option<Alias>,
        #[builder(default = 0)] quantifier_idx: usize,
        #[builder(default = 0)] protocol_idx: usize,
        #[builder(default = 0)] step_idx: usize,
        #[builder(with = FromIterator::from_iter, default = vec![])] cryptography: Vec<usize>,
    ) -> Function {
        let signature = Signature::new(inputs, output);
        let inner = InnerFunction {
            name,
            signature,
            alias,
            flags,
            quantifier_idx,
            protocol_idx,
            step_idx,
            cryptography: cryptography.into(),
        };
        let fun = Function::new(inner);
        self.functions_mut().add(fun.clone());
        fun
    }
}

use crate::problem::function_builder::IsUnset as FunctionBuilderIsUnset;
impl<'a, S> FunctionBuilder<'a, S>
where
    S: function_builder::State,
{
    pub fn flag(mut self, flag: FunctionFlags) -> Self {
        self.flags |= flag;
        self
    }

    pub fn flags(self, flags: implvec!(FunctionFlags)) -> Self {
        flags.into_iter().fold(self, |acc, flag| acc.flag(flag))
    }

    pub fn step(self, idx: usize) -> FunctionBuilder<'a, SetOutput<SetStepIdx<SetAlias<S>>>>
    where
        S::StepIdx: FunctionBuilderIsUnset,
        S::Alias: FunctionBuilderIsUnset,
        S::Output: FunctionBuilderIsUnset,
    {
        self.maybe_alias(None)
            .step_idx(idx)
            .flag(FunctionFlags::STEP)
            .output(Sort::Time)
    }

    /// Try to assign `name` to [Self::name], but generate a fresh name if it's
    /// already taken
    pub fn fresh_name(self, name: &str) -> FunctionBuilder<'a, SetName<S>>
    where
        S::Name: FunctionBuilderIsUnset,
    {
        let name = fresh_name(name, self.self_receiver.function.registered_names());
        self.name(name)
    }

    pub fn and_allocate_cyptographic_assumption(
        self,
        num: usize,
        start: Option<&mut usize>,
    ) -> FunctionBuilder<'a, SetCryptography<S>>
    where
        S::Cryptography: FunctionBuilderIsUnset,
    {
        let len = self.self_receiver.cryptography.len();
        self.self_receiver
            .cryptography
            .extend((0..num).map(|_| Default::default()));
        if let Some(start) = start {
            *start = len
        };
        self.cryptography(len..(len + num))
    }

    pub fn temporary(self) -> Self {
        self.set_temporary(true)
    }

    pub fn set_temporary(mut self, value: bool) -> Self {
        if value {
            self.flags |= FunctionFlags::TEMPORARY
        } else {
            self.flags -= FunctionFlags::TEMPORARY
        }
        self
    }

    pub fn signature(
        self,
        Signature { inputs, output }: Signature,
    ) -> FunctionBuilder<'a, SetInputs<SetOutput<S>>>
    where
        S::Inputs: FunctionBuilderIsUnset,
        S::Output: FunctionBuilderIsUnset,
    {
        self.output(output).inputs(inputs.iter().copied())
    }
}

impl<S> ProblemBuilder<S>
where
    S: problem_builder::State,
{
    /// removes the default cryptography
    pub fn reset_cryptograhy(mut self) -> Self {
        self.cryptography.clear();
        self
    }

    pub fn extend_cryptography(mut self, crypto: implvec!(CryptographicAssumption)) -> Self {
        self.cryptography.extend(crypto);
        self
    }
}

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct CurrentStep {
    /// index in the [Problem]
    pub idx: usize,
    /// specific arguments given for this run
    ///
    /// All the [Function]s are constants
    pub args: Vec<Function>,
}

// #[cfg(test)]
// pub mod test;
