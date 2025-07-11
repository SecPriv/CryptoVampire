use std::borrow::Cow;

use egg::{RecExpr, Var, VarExposed};
use itertools::{Itertools, izip};
use logic_formula::{Destructed, Formula, HeadSk, egg::SimpleDiscriminant};
use utils::{ereturn_if, ereturn_let, implvec};

use crate::{
    LangVar, Problem,
    problem::PRule,
    rules::utils::fresh::{Mode, RefFormulaBuilder},
    terms::{
        Alias, AliasRewrite, EQ, Exists, FOBinder, Function, MACRO_COND, MACRO_MSG, RecFOFormula,
        formula_utils::{offset_rexpr_owned, offset_var},
    },
};

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
        args: implvec!(&'a [LangVar]),
    );

    /// discriminate whether `fun` has a specific subterm
    ///
    /// This is taylored for selecting how to go through things like quantifiers,
    /// macros, etc... See [SyntaxSearcher::is_instance] for actual searching
    fn is_special(&self, pbl: &Problem, fun: &Function) -> bool {
        default_is_special(self, pbl, fun)
    }

    fn inner_search_recexpr(&self, pbl: &Problem, builder: &RefFormulaBuilder, term: &[LangVar]) {
        assert!(builder.current_mode().is_and());
        ereturn_if!(builder.is_saturated());
        ereturn_let!(let Destructed { head: HeadSk::Fun(fun), args} = term.destruct());
        tr!(
            "searching through {}",
            egg::RecExpr::from(term.iter().cloned().collect_vec())
        );
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
        args: implvec!(&'b [LangVar]),
    ) {
        assert!(builder.current_mode().is_and());
        assert!(self.is_special(pbl, &fun));
        tr!("in search_special_recexpr");

        if fun == MACRO_COND || fun == MACRO_MSG {
            todo!()
        } else if let Some(alias) = fun.get_alias() {
            self.search_alias(pbl, builder, alias, args);
        } else if let Some(exists) = fun.get_exists(&pbl.function) {
            self.search_exists(pbl, builder, exists, args);
        }
    }

    fn search_alias<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        Alias(rws): &Alias,
        args: implvec!(&'b [LangVar]),
    ) {
        assert!(builder.current_mode().is_and());
        tr!("in search_alias");
        let args = args.into_iter().collect_vec();
        let max_var = builder.min_var() + 1;
        tr!("max_var = {max_var}");

        let builder = builder.add_node().mode(Mode::Or).build();

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
                .map(|v| offset_var(max_var, *v))
                .collect_vec();
            let from = from
                .iter()
                .map(|f| offset_rexpr_owned(max_var, f.iter().cloned()))
                .collect_vec();
            let to = offset_rexpr_owned(max_var, to.iter().cloned());

            assert_eq!(from.len(), args.len());
            let condition = RecFOFormula::and(
                izip!(args.iter(), from.iter())
                    .map(|(arg, f)| EQ.rapp(vec![RecFOFormula::from(*arg), f.as_ref().into()])),
            );
            let builder = builder
                .add_node()
                .mode(Mode::And)
                .condition(condition)
                .variables(variables)
                .sorts(sorts.iter().cloned())
                .quantifier(FOBinder::Exists)
                .min_var(max_var)
                .build();
            self.inner_search_recexpr(pbl, &builder, &to);
            for arg in &args {
                self.inner_search_recexpr(pbl, &builder, arg);
            }
        }
    }

    fn search_exists<'b>(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        e @ Exists {
            vars,
            bound_var,
            patt,
            ..
        }: &Exists,
        args: implvec!(&'b [LangVar]),
    ) {
        tr!("in search_exists {e}");
        let sort = e.get_var_sort();
        let args = args
            .into_iter()
            .map(Vec::from)
            .map(RecExpr::from)
            .collect_vec();
        let max_var_args = args
            .iter()
            .flat_map(|x| x.free_vars_iter())
            .filter_map(|v| Var::as_u32(&v))
            .max()
            .unwrap_or(0);

        // offsets everything
        let n = u32::max(builder.min_var(), max_var_args) + 1;
        let vars = vars
            .iter()
            .cloned()
            .map(|var| offset_var(n, var))
            .collect_vec();
        let bound_var = offset_var(n, *bound_var);
        let patt = offset_rexpr_owned(n, patt.iter().cloned());

        let content = {
            let subst = izip!(vars.iter().cloned(), args).collect_vec();
            patt.clone().apply_pattern_subst(subst)
        };

        let builder = builder
            .add_node()
            .and()
            .forall()
            .variables([bound_var])
            .sorts([sort])
            .min_var(n)
            .build();

        self.inner_search_recexpr(pbl, &builder, &content);
    }
}
