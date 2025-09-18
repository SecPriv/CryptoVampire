use std::borrow::Cow;

use egg::{RecExpr, Var, VarExposed};
use itertools::{Itertools, izip};
use logic_formula::{Destructed, Formula, HeadSk};
use steel::parser::builder;
use utils::{ereturn_if, ereturn_let, implvec};

use crate::rules::utils::fresh::RefFormulaBuilder;
use crate::terms::utils::offset;
use crate::terms::{
    Alias, AliasRewrite, EQ, Exists, FindSuchThat, FormulaLike, Function, MACRO_COND, MACRO_MSG,
    Quantifier, QuantifierT, RecExprIter, RecFOFormula,
};
use crate::{LangVar, Problem};

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
    fn process_instance<'a>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(RecExprIter<'a, LangVar>),
    );

    /// discriminate whether `fun` has a specific subterm
    ///
    /// This is taylored for selecting how to go through things like quantifiers,
    /// macros, etc... See [SyntaxSearcher::is_instance] for actual searching
    fn is_special(&self, pbl: &Problem, fun: &Function) -> bool {
        default_is_special(self, pbl, fun)
    }

    fn inner_search_recexpr(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        term: RecExprIter<'_, LangVar>,
    ) {
        assert!(builder.current_mode().is_and());
        ereturn_if!(builder.is_saturated());
        tr!(
            "searching through {}",
            egg::RecExpr::from(term.iter().cloned().collect_vec())
        );
        ereturn_let!(let Destructed { head: HeadSk::Fun(fun), args} = term.destruct());
        if self.is_instance(pbl, &fun) {
            self.process_instance(pbl, builder, fun, args);
        } else if self.is_special(pbl, &fun) {
            self.search_special_recexpr(pbl, builder, fun, args);
        } else {
            // base case
            for arg in args {
                self.inner_search_recexpr(pbl, builder, arg);
            }
        }
    }

    fn search_special_recexpr<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(RecExprIter<'b, LangVar>),
    ) {
        assert!(builder.current_mode().is_and());
        assert!(self.is_special(pbl, &fun));
        tr!("in search_special_recexpr");

        if fun == MACRO_COND || fun == MACRO_MSG {
            todo!()
        } else if let Some(alias) = fun.get_alias() {
            self.search_alias(pbl, builder, alias, args);
        } else if fun.is_quantifier() {
            match fun.get_quantifier(&pbl.function) {
                Some(Quantifier::Exists(exists)) => self.search_exists(pbl, builder, exists, args),
                Some(Quantifier::FindSuchThat(fdst)) => self.search_fdst(pbl, builder, fdst, args),
                _ => unreachable!(),
            };
        }
    }

    fn search_alias<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        Alias(rws): &Alias,
        args: implvec!(RecExprIter<'b, LangVar>),
    ) {
        assert!(builder.current_mode().is_and());
        tr!("in search_alias");
        let args = args.into_iter().collect_vec();
        let max_var = builder.min_var() + 1;
        tr!("max_var = {max_var}");

        let builder = builder.add_node().and().build();

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
                .map(|v| offset::var(max_var, *v))
                .collect_vec();
            let from = from
                .iter()
                .map(|f| offset::rexpr_owned(max_var, f.iter().cloned()))
                .collect_vec();
            let to = offset::rexpr_owned(max_var, to.iter().cloned());

            assert_eq!(from.len(), args.len());
            let condition = RecFOFormula::and(
                izip!(args.iter(), from.iter())
                    .map(|(arg, f)| EQ.rapp(vec![arg.clone().into(), f.as_ref().into()])),
            );
            let builder = builder
                .add_node()
                .and()
                // .quantifier(FOBinder::Exists)
                .forall()
                .condition(condition)
                .variables(variables)
                .sorts(sorts.iter().cloned())
                .min_var(max_var)
                .build();
            self.inner_search_recexpr(pbl, &builder, to.as_formula());
            for arg in &args {
                self.inner_search_recexpr(pbl, &builder, arg.clone());
            }
        }
    }

    fn search_exists<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        e: &Exists,
        args: implvec!(RecExprIter<'b, LangVar>),
    ) {
        tr!("in search_exists {e}");
        todo!()
        // let args = args
        //     .into_iter()
        //     .map(Vec::from)
        //     .map(RecExpr::from)
        //     .collect_vec();
        // let max_var_args = args
        //     .iter()
        //     .flat_map(|x| x.free_vars_iter())
        //     .filter_map(|v| Var::as_u32(&v))
        //     .max()
        //     .unwrap_or(0);

        // // offsets everything
        // let n = u32::max(builder.min_var(), max_var_args) + 1;
        // let cvars = e
        //     .cvars()
        //     .iter()
        //     .cloned()
        //     .map(|var| offset::var(n, var))
        //     .collect_vec();
        // let bvars = e
        //     .bvars()
        //     .iter()
        //     .cloned()
        //     .map(|var| offset::var(n, var))
        //     .collect_vec();
        // let patt = offset::rexpr_owned(n, e.patt().iter().cloned());

        // let content = {
        //     let subst = izip!(cvars.iter().cloned(), args).collect_vec();
        //     patt.clone().apply_pattern_subst(subst)
        // };

        // let builder = builder
        //     .add_node()
        //     .and()
        //     .forall()
        //     .min_var(n + (bvars.len() as u32))
        //     .variables(bvars)
        //     .sorts(e.bvars_sorts())
        //     .build();

        // self.inner_search_recexpr(pbl, &builder, &content);
    }

    fn search_fdst<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fdst: &FindSuchThat,
        args: implvec!(RecExprIter<'b, LangVar>),
    ) {
        todo!()
        // tr!("in search_find_such_that {fdst}");
        // let args = args
        //     .into_iter()
        //     .map(Vec::from)
        //     .map(RecExpr::from)
        //     .collect_vec();
        // let max_var_args = args
        //     .iter()
        //     .flat_map(|x| x.free_vars_iter())
        //     .filter_map(|v| Var::as_u32(&v))
        //     .max()
        //     .unwrap_or(0);

        // // offsets everything
        // let n = u32::max(builder.min_var(), max_var_args) + 1;
        // let cvars = fdst
        //     .cvars()
        //     .iter()
        //     .cloned()
        //     .map(|var| offset::var(n, var))
        //     .collect_vec();
        // let bvars = fdst
        //     .bvars()
        //     .iter()
        //     .cloned()
        //     .map(|var| offset::var(n, var))
        //     .collect_vec();

        // let subst = izip!(cvars.iter().cloned(), args).collect_vec();
        // let [condition, then_branch, else_branch] =
        //     [fdst.condition(), fdst.then_branch(), fdst.else_branch()]
        //         .map(|p| offset::rexpr_owned(n, p.iter().cloned()))
        //         .map(|p| p.apply_pattern_subst(subst.clone()));

        // let builder = builder
        //     .add_node()
        //     .and()
        //     .forall()
        //     .min_var(n + (bvars.len() as u32))
        //     .variables(bvars)
        //     .sorts(fdst.bvars_sorts())
        //     .build();

        // self.inner_search_recexpr(pbl, &builder, &condition);
        // let condition = RecFOFormula::from(condition);
        // {
        //     let builder = builder
        //         .add_node()
        //         .and()
        //         .forall()
        //         .condition(condition.clone())
        //         .build();
        //     self.inner_search_recexpr(pbl, &builder, &then_branch);
        // }
        // {
        //     let builder = builder
        //         .add_node()
        //         .and()
        //         .forall()
        //         .condition(!condition)
        //         .build();
        //     self.inner_search_recexpr(pbl, &builder, &else_branch);
        // }
    }
}
