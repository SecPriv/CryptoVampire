use std::borrow::Cow;

use egg::{ENodeOrVar, Pattern, PatternAst, RecExpr, Var, VarExposed};
use golgge::PrologRule;
use itertools::{Itertools, chain, izip};
use logic_formula::{Destructed, Formula, HeadSk, egg::SimpleDiscriminant};
use utils::{ereturn_if, ereturn_let, implvec};

use crate::{
    Lang, LangVar, Problem,
    problem::{PRule, RcRule},
    rexp,
    rules::{
        PRF,
        utils::fresh::{Condition, Mode, RefFormulaBuilder},
    },
    terms::{
        Alias, AliasRewrite, EQ, Exists, FAIL, FOBinder, Function, MACRO_COND, MACRO_MSG, NONCE,
        RecFOFormula, Sort, VAMPIRE, formula_utils::offsets_owned,
    },
};

declare_trace!($"search");



/// default implementation of [SyntaxSearcher::is_special]
#[inline]
pub fn default_is_special<U: SyntaxSearcher + ?Sized>(_self: &U, _pbl: &Problem, fun: &Function) -> bool {
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

            assert_eq!(from.len(), args.len());
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
        self.inner_search_recexpr(pbl, &builder, &content);
    }
}
