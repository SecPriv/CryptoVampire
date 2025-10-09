use std::borrow::Cow;
use std::ops::ControlFlow;

use egg::{EGraph, Id, RecExpr, Var, VarExposed};
use itertools::{Itertools, izip};
use logic_formula::{Destructed, Formula, HeadSk};
use rustc_hash::FxHashMap;
use steel::parser::builder;
use utils::{ereturn_cf, ereturn_if, ereturn_let, implvec};

use crate::problem::PAnalysis;
use crate::protocol::Step;
use crate::rules::utils::fresh::RefFormulaBuilder;
use crate::terms::substitution_utils::AlphaArgs;
use crate::terms::utils::offset;
use crate::terms::{
    Alias, AliasRewrite, BITE, EQ, Exists, FOBinder, FindSuchThat, FormulaLike, Function, HAPPENS,
    LAMBDA_S, LT, MACRO_COND, MACRO_FRAME, MACRO_MSG, MITE, PRED, Quantifier, QuantifierT,
    RecFOFormula, RecFOFormulaQuant, Sort, Variable,
};
use crate::{Lang, LangVar, Problem, fresh, rexp};

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

/// When implementing [SyntaxSearcher] **make sure** each function's
/// pre-implementation does what you what. Think of this more as a macro than a
/// trait.
///
/// It should be easy enough to bail out and nothing should be generic over [SyntaxSearcher]s.
pub trait SyntaxSearcher {
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
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[RecFOFormula],
    ) -> ControlFlow<()>;

    /// discriminate whether `fun` has a specific subterm
    ///
    /// This is taylored for selecting how to go through things like quantifiers,
    /// macros, etc... See [SyntaxSearcher::is_instance] for actual searching
    fn is_special(&self, pbl: &Problem, fun: &Function) -> bool {
        default_is_special(self, pbl, fun)
    }

    fn inner_search_formula(&self, pbl: &Problem, builder: &RefFormulaBuilder, term: RecFOFormula) {
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

    fn search_quantifier(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        quant: RecFOFormulaQuant,
        args: implvec!(RecFOFormula),
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

    fn search_special_recexpr(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(RecFOFormula),
    ) {
        assert!(builder.current_mode().is_and());
        assert!(self.is_special(pbl, &fun));
        tr!("in search_special_recexpr");

        if fun == MACRO_COND || fun == MACRO_MSG {
            todo!()
        } else if let Some(alias) = fun.get_alias() {
            self.search_alias(pbl, builder, alias, args);
        } else if fun.is_quantifier() {
            match fun.get_quantifier(pbl.functions()) {
                // Some(Quantifier::Exists(exists)) => self.search_exists(pbl, builder, exists, args),
                Some(Quantifier::FindSuchThat(fdst)) => {
                    self.search_fdst_alias_function(pbl, builder, fdst, args)
                }
                Some(Quantifier::Exists(_)) => {
                    panic!("exists aliases are no longer needed, please use high order instead")
                }
                _ => unreachable!(),
            };
        }
    }

    fn search_alias(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        alias: &Alias,
        args: implvec!(RecFOFormula),
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
            let from = from.iter().map(RecFOFormula::alpha_rename).collect_vec();
            let to = to.alpha_rename();

            assert_eq!(from.len(), args.len());
            let eqs = izip!(args.iter(), from.iter()).map(|(arg, f)| rexp!((= #arg #f)));
            let condition = rexp!((and #eqs*));

            let builder = builder
                .add_node()
                .and()
                // .quantifier(FOBinder::Exists)
                .forall()
                .condition(condition)
                .variables(variables.iter().cloned())
                .build();
            self.inner_search_formula(pbl, &builder, to);
            for arg in &args {
                self.inner_search_formula(pbl, &builder, arg.clone());
            }
        }
    }

    fn search_exists_alias_function<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        e: &Exists,
        args: implvec!(RecFOFormula),
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

    fn search_fdst_alias_function<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fdst: &FindSuchThat,
        args: implvec!(RecFOFormula),
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
}

pub trait EgraphSearcher: SyntaxSearcher {
    fn process_egraph_instance<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Id],
        variables: &rpds::Queue<Variable>,
    ) -> ControlFlow<()> {
        let args = args
            .iter()
            .map(|&id| expr_of_id(egraph, id, variables))
            .collect_vec();

        self.process_instance(&**egraph.analysis.pbl(), builder, fun, &args)
    }

    fn search_egraph<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        current: Id,
        visited: &rpds::HashTrieSet<Id>,
        variables: &rpds::Queue<Variable>,
    ) {
        tr!("looking at {current:}");
        ereturn_if!(builder.is_saturated());
        ereturn_if!(visited.contains(&current));
        tr!("unskipped");

        let eclass = &egraph[current];
        tr!(
            "current enode has {:} nodes\n({})",
            eclass.nodes.len(),
            expr_of_id(egraph, current, variables)
        );

        // first loop for early exit if necessary
        // This takes care of the cases that replace the whole builder
        for crate::Lang { head, args } in eclass.iter() {
            ereturn_cf!(self.early_egraph_loop(egraph, builder, current, head, args, variables))
        }

        // main loop

        // fresh if indep of *one* of the e-class
        let builder = builder.add_node().or().build();
        let visited = visited.insert(current);
        for crate::Lang { head, args } in eclass.iter() {
            self.main_egraph_loop(egraph, current, &builder, &visited, head, args, variables);
        }
    }

    fn search_frame<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        time: Id,
        ptcl: Id,
        variables: &rpds::Queue<Variable>,
    ) {
        tr!("in frame");
        assert!(builder.current_mode().is_and());
        let time = expr_of_id(egraph, time, variables);

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
                let vars = vars.iter().map(|x| RecFOFormula::Var(x.clone()));
                rexp!((and (HAPPENS (id #(vars.clone())*)) (LT (id #vars*) #time) ))
            };

            let builder = builder
                .add_node().and()
                .condition(condition)
                .variables(vars.clone())
                .forall()
                .build();
            self.inner_search_formula(pbl, &builder, cond.clone());
            self.inner_search_formula(pbl, &builder, msg.clone());
        }
    }

    fn early_egraph_loop<'a>(
        &self,
        egraph: &EGraph<crate::Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        current: Id,
        head: &Function,
        args: &[Id],
        variables: &rpds::Queue<Variable>,
    ) -> ControlFlow<()> {
        tr!(
            "early looking through {head}:{current:}({})",
            args.iter().join(", ")
        );
        if head == &MACRO_FRAME
            && let Some((&time, &ptcl)) = args.iter().collect_tuple()
            && egraph[time].iter().any(|f| f.head == PRED)
        {
            tr!("looking through frame");
            tr!("builder mode {}", builder.borrow().mode());
            self.search_frame(egraph, builder, time, ptcl, variables);
            return ControlFlow::Break(());
        }
        if self.is_instance(&**egraph.analysis.pbl(), head) {
            self.process_egraph_instance(egraph, builder, head, args, variables)
        } else {
            ControlFlow::Continue(())
        }
    }

    fn main_egraph_loop<'a>(
        &self,
        egraph: &EGraph<crate::Lang, PAnalysis<'a>>,
        current: Id,
        builder: &RefFormulaBuilder,
        visited: &rpds::HashTrieSet<Id>,
        head: &Function,
        args: &[Id],
        variables: &rpds::Queue<Variable>,
    ) {
        tr!(
            "looking through {head}:{current:}({})",
            args.iter().join(", ")
        );
        // fresh if indep of all the *arguements*
        if head.is_special_subterm() {
            tr!("is special subterm (flags: {:?})", head.flags);
            // the special cases

            if head == &MITE || head == &BITE {
                self.ite_egraph(egraph, builder, args, visited, variables);
            } else if head == &LAMBDA_S {
                let arg = args[0];
                self.search_egraph(
                    egraph,
                    builder,
                    current,
                    visited,
                    &variables.dequeue().unwrap_or_default(),
                );
            }

            // The rest is taken care of by equality
        } else {
            for arg in args {
                let builder = builder.add_node().and().build();
                self.search_egraph(egraph, &builder, *arg, visited, variables);
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
        visited: &rpds::HashTrieSet<Id>,
        variables: &rpds::Queue<Variable>,
    ) {
        tr!("in ite");
        let builder = builder.add_node().and().build();
        let (c, l, r) = args.iter().copied().collect_tuple().unwrap();

        self.search_egraph(egraph, &builder, c, visited, variables);

        let c = expr_of_id(egraph, c, variables);

        {
            // pos
            let builder = builder
                .add_node()
                .or()
                .forall()
                .condition(c.clone())
                .build();
            self.search_egraph(egraph, &builder, l, visited, variables);
        }
        {
            // neg
            let builder = builder.add_node().or().forall().condition(!c).build();
            self.search_egraph(egraph, &builder, r, visited, variables);
        }
    }

    /// Builds the subterm of a quantifier in the case of an eclass
    ///
    /// `visisted` must already be updated
    fn binder_egraph<'a>(
        &self,
        egraph: &EGraph<Lang, PAnalysis<'a>>,
        builder: &RefFormulaBuilder,
        quant: FOBinder,
        args: &[Id],
        visited: &rpds::HashTrieSet<Id>,
        variables: &rpds::Queue<Variable>,
    ) {
        tr!("in {quant}");
        let mut args = args.iter();

        let sorts = Sort::list_from_egg(egraph, *args.next().unwrap()).unwrap();
        let nvariables = sorts.into_iter().map(|s| fresh!(s)).collect_vec();
        let variable = nvariables
            .iter()
            .fold(variables.clone(), |acc, v| acc.enqueue(v.clone()));

        match quant {
            FOBinder::Exists | FOBinder::Forall => {
                let builder = builder.add_node().forall().variables(nvariables).build();
                self.search_egraph(egraph, &builder, *args.next().unwrap(), visited, variables);
            }
            FOBinder::FindSuchThat => {
                assert!(builder.is_and());
                let (c, t, e) = args.cloned().collect_tuple().unwrap();
                {
                    // cond
                    let builder = builder
                        .add_node()
                        .forall()
                        .variables(nvariables.clone())
                        .build();
                    self.search_egraph(egraph, &builder, c, visited, variables);
                }

                ereturn_if!(builder.is_saturated());
                let cond = expr_of_id(egraph, c, &variable);
                {
                    // then
                    let builder = builder
                        .add_node()
                        .forall()
                        .variables(nvariables.clone())
                        .condition(cond.clone())
                        .build();
                    self.search_egraph(egraph, &builder, t, visited, variables);
                }
                {
                    // else
                    let builder = builder
                        .add_node()
                        .condition(rexp!((forall #nvariables (not #cond))))
                        .build();
                    self.search_egraph(egraph, &builder, e, visited, variables);
                }
            }
        }
    }
}

pub fn expr_of_id<'a>(
    egraph: &EGraph<Lang, PAnalysis<'a>>,
    id: Id,
    variables: &rpds::Queue<Variable>,
) -> RecFOFormula {
    RecFOFormula::try_from_id_with_vars(egraph, id, variables).unwrap()
}
