use std::borrow::Cow;
use std::fmt::Debug;
use std::num::NonZeroUsize;
use std::rc::Rc;

use bon::bon;
use cryptovampire_smt::Smt;
use egg::{EGraph, RecExpr};
use golgge::{Program, Rule};
use itertools::{Itertools, chain};
use log::{log_enabled, trace};
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
    FunctionCollection, FunctionFlags, HAPPENS, INIT, InnerFunction, MACRO_FRAME, PRED, Quantifier,
    QuantifierT, QuantifierTranslator, RecFOFormula, Rewrite, Signature, Sort, TRUE, UNFOLD_MSG,
};
use crate::utils::fresh_name;
use crate::{Configuration, Lang, MSmt, mk_signature, rexp, smt};

mod analysis;
pub use analysis::{PAnalysis, PRule, RcRule};

mod state;
pub use state::ProblemState;

declare_trace!($"problem");

/// A problem for the solver to solve
///
/// This struct contains all the information needed to run the solver.
/// It contains the protocols to prove indistinguishability on, the functions,
/// the cryptographic assumptions, and the extra rules, rewrites, and SMT formulas.
#[non_exhaustive]
pub struct Problem {
    /// The configuration (e.g., cli arguments and such)
    pub config: Configuration,
    /// The protocols we want to prove indistiguishability on
    ///
    /// The vector must be at least 2 long
    protocols: Vec<Protocol>,
    /// The functions
    function: FunctionCollection,

    /// The cryptographic assumptions
    cryptography: Vec<CryptographicAssumption>,

    /// Extra rules to add to the solver
    extra_rules: Vec<RcRule>,
    /// Extra rewrites to add to the solver
    extra_rewrite: Vec<Rewrite>,
    /// Extra SMT formulas to add to the solver
    extra_smt: Vec<MSmt>,

    /// cache for the smt prelude
    smt_prelude: Option<Vec<MSmt>>,

    /// the current step in the run (if any)
    current_step: Option<CurrentStep>,

    /// a cache for the quantifiers
    quantifier_cache: Vec<(RecFOFormula, Function)>,

    pub state: ProblemState,
}

impl Default for Problem {
    /// Creates a new `Problem` with default values.
    fn default() -> Self {
        Self::builder().build()
    }
}

impl Problem {
    /// Checks if the protocols are compatible
    ///
    /// This function checks that all the protocols are compatible with each other.
    /// Two protocols are compatible if they have the same steps and the same
    /// variables in each step.
    pub fn valid(&self) -> bool {
        self.protocols
            .iter()
            .tuple_windows()
            .all(|(a, b)| Protocol::are_compatible(a, b))
    }

    /// Returns the `init` function
    pub fn get_init_fun(&self) -> &Function {
        &INIT
    }

    /// Build a [Program] to use
    pub fn mk_program<'a>(&'a mut self) -> Program<Lang, PAnalysis<'a>> {
        self.state.reset();

        let exec = SmtRunner::new(self);
        let vampire_rule = VampireRule::builder().exec(exec.clone()).build();
        let fresh_rule = FreshNonce::builder().exec(exec.clone()).build();

        let eq_rules = mk_default_rewrites(self);
        let rules = mk_default_prolog_rules(self);
        let rules: Vec<Rc<dyn Rule<_, _>>> =
            chain![rules, [vampire_rule.into_mrc(), fresh_rule.into_mrc()]].collect_vec();

        let golgge_config = {
            let Configuration {
                node_limit,
                time_limit,
                iter_limit,
                trace,
                
                ..
            } = self.config;
            golgge::Config::builder()
                .node_limit(node_limit)
                .iter_limit(iter_limit)
                .time_limit(time_limit)
                .trace_prolog(trace)
                .build()
        };

        golgge::Program::build()
            .eq_rules(eq_rules)
            .rules(rules)
            .config(golgge_config)
            .egraph(EGraph::new(PAnalysis::builder().pbl(self).build()).with_explanations_enabled())
            .call()
    }

    /// Run the solver on the given protocols
    ///
    /// This function runs the solver on the protocols `p1` and `p2`.
    /// It returns `true` if the protocols are indistinguishable, `false` otherwise.
    ///
    /// # Panics
    ///
    /// This function will panic if `p1` or `p2` are not valid indices for the
    /// protocols in the `Problem`.
    pub fn run_solver(&mut self, p1: usize, p2: usize) -> bool {
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

    /// Computes the SMT prelude if it hasn't been computed yet and caches it.
    fn compute_smt_prelude(&mut self) {
        if self.smt_prelude.is_none() {
            self.find_temp_quantifiers(&[]);
            let prelude = mk_prelude(self).collect();
            self.smt_prelude = Some(prelude)
        }
    }

    /// Returns the SMT prelude if it has been computed
    pub fn maybe_get_smt_prelude(&self) -> Option<&[MSmt]> {
        self.smt_prelude.as_deref()
    }

    /// Returns the SMT prelude, computing it if necessary
    pub fn get_smt_prelude(&mut self) -> &[MSmt] {
        self.compute_smt_prelude();
        self.smt_prelude.as_ref().unwrap()
    }

    /// Clears the SMT prelude
    pub fn clear_smt_prelude(&mut self) {
        self.smt_prelude = None;
    }

    /// Returns the extra SMT formulas
    pub fn extra_smt(&self) -> &[MSmt] {
        &self.extra_smt
    }

    /// Returns a mutable reference to the extra SMT formulas
    pub fn extra_smt_mut(&mut self) -> &mut Vec<MSmt> {
        self.clear_smt_prelude();
        &mut self.extra_smt
    }

    /// Returns the extra rewrites
    pub fn extra_rewrite(&self) -> &[Rewrite] {
        &self.extra_rewrite
    }

    /// Returns a mutable reference to the extra rewrites
    pub fn extra_rewrite_mut(&mut self) -> &mut Vec<Rewrite> {
        self.clear_smt_prelude();
        &mut self.extra_rewrite
    }

    /// Returns the extra rules
    pub fn extra_rules(&self) -> &[RcRule] {
        &self.extra_rules
    }

    /// Returns a mutable reference to the extra rules
    pub fn extra_rules_mut(&mut self) -> &mut Vec<RcRule> {
        &mut self.extra_rules
    }

    /// Returns the protocols
    pub fn protocols(&self) -> &[Protocol] {
        &self.protocols
    }

    /// Returns a mutable reference to the protocol at the given index
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
    /// # Panics
    ///
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

    /// Returns an iterator over the steps of the first protocol
    pub fn steps(&self) -> Option<impl Iterator<Item = Function> + use<'_>> {
        Some(
            self.protocols()
                .first()?
                .steps()
                .iter()
                .map(|Step { id, .. }| id.clone()),
        )
    }

    /// Returns the number of steps in the first protocol
    ///
    /// # Panics
    ///
    /// This function will panic if the first protocol has no steps.
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

    /// Returns the number of protocols
    pub fn num_protocols(&self) -> usize {
        self.protocols().len()
    }

    /// Returns the cryptographic assumptions
    pub fn cryptography(&self) -> &[CryptographicAssumption] {
        &self.cryptography
    }

    /// Returns a mutable reference to the cryptographic assumption at the given index
    pub fn cryptography_mut(&mut self, index: usize) -> Option<&mut CryptographicAssumption> {
        self.cryptography.get_mut(index)
    }

    /// Extends the cryptographic assumptions with `N` new default assumptions
    ///
    /// Returns an array of the indices of the new assumptions.
    pub fn extend_cryptography<const N: usize>(&mut self) -> [usize; N] {
        let ret = std::array::from_fn(|i| i + self.cryptography.len());
        self.cryptography.extend(ret.map(|_| Default::default()));
        ret
    }

    /// Returns a reference to the current step in the problem's execution, if any.
    #[allow(dead_code)]
    pub(crate) fn current_step(&self) -> Option<&CurrentStep> {
        self.current_step.as_ref()
    }

    /// Returns the function collection
    pub fn functions(&self) -> &FunctionCollection {
        &self.function
    }

    /// Returns a mutable reference to the function collection
    pub fn functions_mut(&mut self) -> &mut FunctionCollection {
        self.clear_smt_prelude();
        &mut self.function
    }

    /// Finds all the temporary quantifiers in the problem and adds them to the cache
    pub fn find_temp_quantifiers(&mut self, extra: &[RecFOFormula]) {
        if extra.is_empty() && self.smt_prelude.is_some() {
            return;
        }

        tr!("looks for quantifier candidates in:");
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
                    tr!("{a:?}");
                    pile.push(a.clone());
                }
            }
            pile
        };
        tr!(
            "found quantifiers!:\n{}",
            chain![
                quantifiers.iter(),
                self.quantifier_cache.iter().map(|(q, _)| q)
            ]
            .join("\n")
        );

        if quantifiers.is_empty() {
            return;
        }

        tr!("generate names for quantifers");
        for q in quantifiers.iter() {
            econtinue_let!(let RecFOFormula::Quantifier { vars, arg, head: FOBinder::FindSuchThat } = q);
            let cvars = q.free_vars_iter().unique().cloned();
            let bvars = vars.iter().cloned();

            let find = FindSuchThat::insert()
                .pbl(self)
                .bvars(bvars)
                .cvars(cvars)
                .temporary(true)
                .call();
            find.set_condition(arg[0].clone());
            find.set_then_branch(arg[1].clone());
            find.set_else_branch(arg[2].clone());
            tr!("adding newfound quantifier:\n{find:#?}\n\tfrom{q}");
            let tlf = find.top_level_function().clone();
            self.quantifier_cache.push((q.clone(), tlf));
        }
        self.clear_smt_prelude();
    }

    /// Clears the temporary quantifiers from the cache
    pub fn clear_temp_quantifiers(&mut self) {
        self.quantifier_cache.clear();
        self.clear_smt_prelude();
    }

    /// list all the `RecFOFormula` stored in this `Self`
    pub fn list_all_terms(&self) -> impl Iterator<Item = &RecFOFormula> {
        chain![
            self.protocols()
                .iter()
                .flat_map(|p| p.steps().iter())
                .flat_map(|s| [&s.cond, &s.msg].into_iter()),
            self.extra_rewrite().iter().flat_map(
                |Rewrite {
                     from,
                     to,
                     prolog_only,
                     ..
                 }| {
                    (!prolog_only)
                        .then_some([from, to].into_iter())
                        .into_iter()
                        .flatten()
                }
            )
        ]
    }
}

/// This implementation allows to translate quantifiers using the cache
impl QuantifierTranslator for Problem {
    /// Attempts to translate a given quantifier formula using the cached quantifiers.
    ///
    /// Returns `Some(translated_formula)` if a translation is found, otherwise `None`.
    fn try_translate(&self, formula: &RecFOFormula) -> Option<crate::terms::RecFOFormula> {
        tr!("try translate:\n{formula}");
        if log_enabled!(log::Level::Trace) {
            let mut p = String::new();
            for (q, f) in &self.quantifier_cache {
                p += &format!("{} => {q}\n", f.name);
            }
            tr!("available quantifiers:\n{p}")
        }

        let (subst, fun) = self
            .quantifier_cache
            .iter()
            .find_map(|(cached, fun)| cached.unify(formula).map(|subst| (subst, fun.clone())))?;
        let q = fun.get_quantifier(self.functions()).unwrap();

        let Quantifier::FindSuchThat(q2) = q else {
            unreachable!()
        };
        let cond = q2.condition().unwrap();

        tr!(
            "quantifier translation:\n\tterm:\n\t{formula}\n\tfunction:{}\n\t\t(cond: \
             {cond})\n\t\tcvars:[{}],\n\tsubstitution:\n{}",
            q.top_level_function().name,
            q.cvars().iter().map(|v| format!("{v:?}")).join(", "),
            subst
                .iter()
                .map(|(v, f)| format!("\t{v:?} => {f}"))
                .join(",\n")
        );

        let args = q
            .cvars()
            .iter()
            .map(|v| {
                subst
                    .get(v)
                    .cloned()
                    .unwrap_or(RecFOFormula::Var(v.clone()))
            })
            .collect_vec();
        let args = args.iter().cloned();

        tr!("arg vars: [{}]", args.clone().join(", "));

        let sks = q.skolems().iter().map(|sk| rexp!((sk #(args.clone())*)));
        let tlf = q.top_level_function();

        Some(rexp!((tlf #(args.clone())* #sks*)))
    }
}

impl Debug for Problem {
    /// Formats the `Problem` for debugging purposes.
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
    /// Returns a reference to the `FunctionCollection` within the `Problem`.
    fn as_ref(&self) -> &FunctionCollection {
        &self.function
    }
}

impl AsMut<FunctionCollection> for Problem {
    /// Returns a mutable reference to the `FunctionCollection` within the `Problem`.
    fn as_mut(&mut self) -> &mut FunctionCollection {
        &mut self.function
    }
}

#[bon]
impl Problem {
    fn default_cryptography() -> Vec<CryptographicAssumption> {
        vec![CryptographicAssumption::NoGuessingTh]
    }

    /// Creates a new `Problem` instance with the specified components.
    ///
    /// This is typically used with the `ProblemBuilder` for a more ergonomic construction.
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
            state: Default::default(),
        }
    }

    /// Declares a new function
    ///
    /// This function returns a [FunctionBuilder] that can be used to build a new function.
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
    /// Adds a flag to the function
    pub fn flag(mut self, flag: FunctionFlags) -> Self {
        self.flags |= flag;
        self
    }

    /// Adds multiple flags to the function
    pub fn flags(self, flags: implvec!(FunctionFlags)) -> Self {
        flags.into_iter().fold(self, |acc, flag| acc.flag(flag))
    }

    /// Sets the function as a step function
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

    /// Allocates a new cryptographic assumption and assigns it to the function
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

    /// Sets the function as temporary
    pub fn temporary(self) -> Self {
        self.set_temporary(true)
    }

    /// Sets the function as temporary or not
    pub fn set_temporary(mut self, value: bool) -> Self {
        if value {
            self.flags |= FunctionFlags::TEMPORARY
        } else {
            self.flags -= FunctionFlags::TEMPORARY
        }
        self
    }

    /// Sets the signature of the function
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

    /// extends the cryptography with the given assumptions
    pub fn extend_cryptography(mut self, crypto: implvec!(CryptographicAssumption)) -> Self {
        self.cryptography.extend(crypto);
        self
    }
}

/// Represents the current step in the execution of the problem
#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct CurrentStep {
    /// The index of the current step in the problem.
    pub idx: usize,
    /// Specific arguments given for this run. All the [Function]s are constants.
    pub args: Vec<Function>,
}

// #[cfg(test)]
// pub mod test;
