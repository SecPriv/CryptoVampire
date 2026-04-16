use std::borrow::Cow;
use std::ops::ControlFlow;

use egg::{EGraph, Id};
use itertools::{Itertools, izip};
use logic_formula::{AsFormula, Destructed, HeadSk};
use rustc_hash::{FxHashMap, FxHashSet};
use utils::{ereturn_cf, ereturn_if, implvec};

use crate::libraries::memory_cells;
use crate::libraries::utils::{
    DefaultAux, FormulaBuilderAux, FormulaBuilderFlags, RefFormulaBuilder, get_protocol,
};
use crate::problem::PAnalysis;
use crate::protocol::{Protocol, Step};
use crate::runners::SmtRunner;
use crate::terms::{
    Alias, AliasRewrite, AlphaArgs, BITE, Exists, FOBinder, FindSuchThat, Formula, Function,
    HAPPENS, LAMBDA_S, LEQ, MACRO_COND, MACRO_EXEC, MACRO_FRAME, MACRO_INPUT, MACRO_MEMORY_CELL,
    MACRO_MSG, MITE, PRED, Quantifier, QuantifierT, RecFOFormulaQuant, Sort, Variable,
};
use crate::{CVProgram, Lang, MSmt, Problem, fresh, rexp};

declare_trace!($"search");

/// default implementation of [SyntaxSearcher::is_special]
#[inline]
pub fn default_is_special<U: SyntaxSearcher + ?Sized>(
    _self: &U,
    _pbl: &Problem,
    fun: &Function,
) -> bool {
    fun.is_special_subterm()
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub enum MsgOrCond {
    Msg,
    Cond,
}

pub type RBFormula<U> = RefFormulaBuilder<<U as SyntaxSearcher>::Aux>;

/// When implementing [SyntaxSearcher] **make sure** each function's
/// pre-implementation does what you what. Think of this more as a macro than a
/// trait.
///
/// It should be easy enough to bail out and nothing should be generic over [SyntaxSearcher]s.
pub trait SyntaxSearcher {
    type Aux: FormulaBuilderAux + Clone + Default;

    /// an name for debugging
    fn debug_name<'a>(&'a self) -> Cow<'a, str>;

    /// Did the search "succeeded" in searching somethign?
    ///
    /// This will eventually call [SyntaxSearcher::process_instance].
    fn is_instance(&self, pbl: &Problem, fun: &Function) -> bool;

    /// Process a potential instance
    ///
    /// Is only called if [SyntaxSearcher::process_instance] succeeds
    ///
    /// Return whether too keep looping (true if skip)
    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()>;

    /// discriminate whether `fun` has a specific subterm
    ///
    /// This is taylored for selecting how to go through things like quantifiers,
    /// macros, etc... See [SyntaxSearcher::is_instance] for actual searching
    fn is_special(&self, pbl: &Problem, fun: &Function) -> bool {
        default_is_special(self, pbl, fun)
    }

    /// Recursively searches a `RecFOFormula` for relevant instances.
    ///
    /// This function traverses the formula, identifying instances that match `is_instance`
    /// or special subterms handled by `search_special_recexpr`.
    fn inner_search_formula(&self, pbl: &Problem, builder: &RBFormula<Self>, term: Formula) {
        assert!(builder.current_mode().is_and());
        ereturn_if!(builder.is_saturated());
        tr!("searching through {term}");

        let Destructed { head, args } = term.destruct();
        let args = args.into_iter().collect_vec();
        match head {
            HeadSk::Fun(fun) => {
                if self.is_instance(pbl, &fun) {
                    ereturn_cf!(self.process_instance(pbl, builder, &fun, &args))
                }

                if self.is_special(pbl, &fun) {
                    self.search_special_recexpr(pbl, builder, fun, args);
                } else {
                    // base case
                    for arg in args {
                        self.inner_search_formula(pbl, builder, arg);
                    }
                }
            }
            HeadSk::Quant(quant) => {
                self.search_quantifier(pbl, builder, quant, args);
            }
            _ => {}
        }
    }

    /// Searches within a quantifier formula, handling different binder types.
    ///
    /// This method recursively calls `inner_search_formula` on the quantifier's arguments,
    /// adjusting the builder's context (e.g., adding variables, conditions).
    fn search_quantifier(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        quant: RecFOFormulaQuant,
        args: implvec!(Formula),
    ) {
        let RecFOFormulaQuant { quantifier, vars } = quant;

        match quantifier {
            FOBinder::Exists | FOBinder::Forall => {
                let builder = builder.add_node().forall().variables(vars).and().build();
                self.inner_search_formula(pbl, &builder, args.into_iter().next().unwrap());
            }
            FOBinder::FindSuchThat => {
                let (cond, t, e) = args.into_iter().collect_tuple().unwrap();
                {
                    // condition
                    let builder = builder.add_node().forall().variables(vars.clone()).build();
                    self.inner_search_formula(pbl, &builder, cond.clone());
                }
                {
                    // then
                    let builder = builder
                        .add_node()
                        .forall()
                        .variables(vars.clone())
                        .condition(cond.clone())
                        .build();
                    self.inner_search_formula(pbl, &builder, t);
                }
                {
                    // else
                    let builder = builder
                        .add_node()
                        .condition(rexp!((forall #vars (not #cond))))
                        .build();
                    self.inner_search_formula(pbl, &builder, e);
                }
            }
        }
    }

    /// Handles searching within special `RecFOFormula` expressions.
    ///
    /// This method dispatches to specific handlers for aliases, quantifiers, and other special functions.
    fn search_special_recexpr(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        fun: Function,
        args: implvec!(Formula),
    ) {
        assert!(builder.current_mode().is_and());
        assert!(self.is_special(pbl, &fun));
        tr!("in search_special_recexpr");

        if fun == MACRO_COND || fun == MACRO_MSG {
            let kind = fun.try_into().unwrap();
            let (time, ptcl) = args
                .into_iter()
                .collect_tuple()
                .expect("terms should be well typed");
            self.search_msg_cond_macro(pbl, builder, kind, ptcl, time)
        } else if fun == MACRO_MEMORY_CELL {
            let (cell, time, ptcl) = args
                .into_iter()
                .collect_tuple()
                .expect("terms should be well typed");
            self.search_memory_cell(pbl, builder, cell, ptcl, time);
        } else if fun == MACRO_FRAME || fun == MACRO_EXEC || fun == MACRO_INPUT {
            let (mut time, ptcl) = args
                .into_iter()
                .collect_tuple()
                .expect("terms should be well typed");

            if fun == MACRO_INPUT {
                time = rexp!((PRED #time));
            }
            let ptcl = Protocol::from_formula(pbl, &ptcl).expect("proctols should be concrete");

            self.search_frame(pbl, builder, ptcl, &time);
        } else if let Some(alias) = fun.get_alias() {
            self.search_alias(pbl, builder, alias, args);
        } else if fun.is_quantifier() {
            match fun.get_quantifier(pbl.functions()) {
                Some(Quantifier::FindSuchThat(fdst)) => {
                    self.search_fdst_alias_function(pbl, builder, fdst, args)
                }
                Some(Quantifier::Exists(_)) => {
                    panic!(
                        "exists aliases are no longer needed and deprecated, please use high \
                         order instead"
                    )
                }
                _ => unreachable!(),
            };
        }
    }

    fn search_msg_cond_macro(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        kind: MsgOrCond,
        ptcl: Formula,
        time: Formula,
    ) {
        // NB: we assume well-formed-ness to ensure terminiation. Otherwise it is easy to make this loop forever.
        tr!("in search_msg_cond_macro");
        match (ptcl, time) {
            (Formula::App { head: ptcl, .. }, Formula::App { head: step, args }) => {
                let ptcl_idx = ptcl
                    .get_protocol_index()
                    .expect("the protocol field should be a concrete protocol");
                let step_idx = step
                    .get_step_index()
                    .expect("the time field should be a concrete step");
                let step = &pbl.protocols()[ptcl_idx].steps()[step_idx];
                let t = match kind {
                    MsgOrCond::Cond => &step.cond,
                    MsgOrCond::Msg => &step.msg,
                };
                let mut subst = Default::default();
                let t = t.alpha_rename_if_with(&mut subst, &mut |_| true);

                let args_eqs = izip!(args.iter(), &step.vars).map(|(arg, var)| {
                    let narg = subst.get(var).unwrap().clone();
                    rexp!((= #arg #narg))
                });

                let builder = builder
                    .add_node()
                    .variables(subst.values().cloned())
                    .condition(Formula::and(args_eqs))
                    .build();
                self.inner_search_formula(pbl, &builder, t);
            }
            _ => unreachable!("protocols should be well formed"),
        }
    }

    fn search_memory_cell(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        cell: Formula,
        ptcl: Formula,
        time: Formula,
    ) {
        tr!("in search_memory_cell {cell}");
        let Formula::App {
            head: cell_head,
            args: cell_args,
        } = cell
        else {
            unreachable!("cells should be conctrete")
        };
        assert!(cell_head.is_memory_cell());

        let ptcl = Protocol::from_formula(pbl, &ptcl).expect("proctols should be concrete");

        match time {
            Formula::App {
                head: step_head,
                args: step_args,
            } if step_head == PRED => {
                let time = &step_args[0];
                memory_cells::search_pred_memory_cell(
                    self, pbl, builder, cell_head, cell_args, ptcl, time,
                );
            }
            Formula::App {
                head: ref step_head,
                args,
            } if step_head.is_step() => {
                let step = &ptcl.steps()[step_head.get_step_index().unwrap()];
                memory_cells::search_concrete_memory_cell(
                    self, pbl, builder, cell_head, cell_args, ptcl, step, args,
                );
            }
            _ => unreachable!("time field should be a 'pred(step)' or a concrete step"),
        }
    }

    /// Searches within an alias function, applying its rewrite rules.
    ///
    /// This method expands the alias according to its rewrite rules and recursively searches the resulting formulas.
    fn search_alias(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        alias: &Alias,
        args: implvec!(Formula),
    ) {
        let Alias(rws) = alias; // <- because of rustfmt
        assert!(builder.current_mode().is_and());
        tr!("in search_alias");
        let args = args.into_iter().collect_vec();

        let builder = builder.add_node().and().build();

        for AliasRewrite {
            from,
            to,
            variables,
        } in rws.iter()
        {
            let mut subst = Default::default();
            let from = from
                .iter()
                .map(|f| f.alpha_rename_if_with(&mut subst, &mut |_| true))
                .collect_vec();
            let to = to.alpha_rename_if_with(&mut subst, &mut |_| true);

            debug_assert_eq!(
                FxHashSet::from_iter(variables.iter()),
                FxHashSet::from_iter(subst.keys().copied())
            );
            let variables = subst.into_values();

            assert_eq!(from.len(), args.len());
            let eqs = izip!(args.iter(), from.iter()).map(|(arg, f)| rexp!((= #arg #f)));
            let condition = rexp!((and #eqs*));

            let builder = builder
                .add_node()
                .and()
                // .quantifier(FOBinder::Exists)
                .forall()
                .condition(condition)
                .variables(variables)
                .build();
            self.inner_search_formula(pbl, &builder, to);
            for arg in &args {
                self.inner_search_formula(pbl, &builder, arg.clone());
            }
        }
    }

    /// Searches within an existential quantifier alias function.
    ///
    /// This method substitutes the bound variables with the provided arguments and recursively searches the resulting formula.
    fn search_exists_alias_function<'b>(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        e: &Exists,
        args: implvec!(Formula),
    ) {
        tr!("in search_exists {e}");
        ::log::warn!("into an exists alias functions, thoses are deprecated");

        let subst = izip!(e.cvars().iter().cloned(), args).collect_vec();
        let mut alpha_susbt = FxHashMap::default();

        let arg = e
            .patt()
            .expect("the quantifier must be initialised")
            // alpha-rename the bound variables
            .alpha_rename_if_with(&mut alpha_susbt, &mut |AlphaArgs { var, .. }| {
                e.bvars().contains(var)
            })
            // replace the bound variables by the arguments to the `fdst` function
            .subst(&subst);

        let bvars = alpha_susbt.keys().map(|v| (*v).clone());
        self.inner_search_formula(pbl, builder, rexp!((exists #bvars #arg)));
    }

    /// Searches within a `FindSuchThat` alias function.
    ///
    /// This method substitutes the bound variables and recursively searches the condition, then, and else branches.
    fn search_fdst_alias_function<'b>(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        fdst: &FindSuchThat,
        args: implvec!(Formula),
    ) {
        tr!("in search_find_such_that fucntion {fdst}");

        let subst = izip!(fdst.cvars().iter().cloned(), args).collect_vec();
        let mut alpha_susbt = FxHashMap::default();

        let [condition, then_branch, else_branch] =
        // alpha-rename the bound variables
        {
            fdst.arguments()
                .expect("the quantifier must be initialised")
                .map(|x| {
                    x.alpha_rename_if_with(&mut alpha_susbt, &mut |AlphaArgs { var, .. }| {
                        fdst.bvars().contains(var)
                    })
                })
        }
        // replace the bound variables by the arguments to the `fdst` function
        .map(|x| x.subst(&subst));

        let bvars = alpha_susbt.keys().map(|v| (*v).clone());
        self.inner_search_formula(
            pbl,
            builder,
            rexp!((find_such_that #bvars #condition #then_branch #else_branch)),
        );
    }

    /// search `frame_<ptcl>@<time>`,
    ///
    /// This method iterates through the steps of the protocol and recursively searches
    /// their conditions and messages, applying appropriate conditions based on the frame.
    ///
    /// NB: This doesn't try to unfold (so `time` can a variables)
    fn search_frame(
        &self,
        pbl: &Problem,
        builder: &RBFormula<Self>,
        ptcl: &Protocol,
        time: &Formula,
    ) {
        ereturn_if!(
            builder.is_saturated()
                || builder
                    .flags()
                    .intersects(FormulaBuilderFlags::NO_THROUGH_PREVIOUS_BODY)
        );
        tr!("in frame");
        let builder = builder.ensure_and();

        // for each step we switch to `search_recexpr` on its message
        for Step {
            id,
            vars,
            cond,
            msg,
            ..
        } in ptcl.steps()
        {
            // build the condition object
            let condition = {
                let vars = vars.iter().map(|x| Formula::Var(x.clone()));
                rexp!((and (HAPPENS (id #(vars.clone())*)) (LEQ (id #vars*) #time) ))
            };

            let builder = builder
                .add_node()
                .and()
                .condition(condition)
                .variables(vars.clone())
                .forall()
                .add_flag(FormulaBuilderFlags::NO_THROUGH_PREVIOUS_BODY)
                .build();
            self.inner_search_formula(pbl, &builder, cond.clone());
            self.inner_search_formula(pbl, &builder, msg.clone());
        }
    }

    /// Returns an iterator of formula instead of a large conjunctrion
    /// Searches for PRF-related conditions at a specific timepoint within a protocol.
    fn search_timepoint<'a>(
        &'a self,
        pbl: &'a Problem,
        ptcl: &'a Protocol,
        time: Formula,
        hyp: Formula,
    ) -> impl Iterator<Item = Formula> + use<'a, Self> {
        tr!("searching protocol {}", ptcl.name());
        ptcl.steps()
            .iter()
            .flat_map(
                move |step @ Step {
                          id,
                          vars,
                          cond,
                          msg,
                          ..
                      }| {
                    let vars = vars.iter().map(|v| Formula::Var(v.clone()));
                    let s = rexp!((id #vars*));

                    let condition = rexp!((and #hyp (HAPPENS #s) (LEQ #s #time)));
                    [
                        (condition.clone(), cond, step),
                        (condition.clone(), msg, step),
                    ]
                    .into_iter()
                },
            )
            .map(|(condition, to_search, Step { vars, .. })| {
                let builder = RefFormulaBuilder::builder()
                    .condition(condition)
                    .variables(vars.clone())
                    .forall()
                    .add_flag(FormulaBuilderFlags::NO_THROUGH_PREVIOUS_BODY)
                    .build();
                self.inner_search_formula(pbl, &builder, to_search.clone());
                builder.into_inner().unwrap().into_formula()
            })
            .flat_map(|x: Formula| x.split_conjunction())
    }

    fn search_id_timepoint<'a, 'b, 'c>(
        &'b self,
        prgm: &'c mut CVProgram<'a>,
        exec: &'b SmtRunner,
        ptcl: Id,
        time: Formula,
        hyp: Formula,
    ) -> Option<bool> {
        let ptcl = get_protocol(prgm.egraph(), ptcl)?;
        let queries = self
            .search_timepoint(prgm.egraph().analysis.pbl(), ptcl, time, hyp)
            .collect_vec();
        let pbl = prgm.egraph_mut().analysis.pbl_mut();
        let result = exec.iter_run_to_dependancy(pbl, queries).is_axioms();
        pbl.clear_temp_quantifiers();

        // pbl.find_temp_quantifiers(&queries);

        // let result = queries.into_iter().all(|query| {
        //     let query = query.as_smt(*pbl).unwrap();
        //     exec.run_to_dependancy(pbl, query).is_axioms()
        // });
        // pbl.clear_temp_quantifiers();
        Some(result)
    }

    fn search_term<'a, 'b, 'c>(
        &'b self,
        prgm: &'c mut CVProgram<'a>,
        exec: &'b SmtRunner,
        term: Formula,
        hyp: Formula,
    ) -> Option<bool> {
        let builder = RBFormula::<Self>::builder().condition(hyp).build();
        let pbl = prgm.egraph_mut().analysis.pbl();
        self.inner_search_formula(pbl, &builder, term);

        let query = builder.into_inner().unwrap().into_formula();
        let queries = query.into_iter_conjunction();
        let _ = pbl;
        let pbl = prgm.egraph_mut().analysis.pbl_mut();
        let result = exec.iter_run_to_dependancy(pbl, queries).is_axioms();
        pbl.clear_temp_quantifiers();
        Some(result)
    }
}

impl TryFrom<Function> for MsgOrCond {
    type Error = Function;

    fn try_from(value: Function) -> Result<Self, Self::Error> {
        if value == MACRO_COND {
            Ok(Self::Cond)
        } else if value == MACRO_MSG {
            Ok(Self::Msg)
        } else {
            Err(value)
        }
    }
}
