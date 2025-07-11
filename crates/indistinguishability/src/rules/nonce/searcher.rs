use super::*;
use crate::{
    Lang, LangVar, Problem,
    problem::PAnalysis,
    protocol::Step,
    rules::{
        nonce::searcher::nonce_builder::SetContent,
        utils::{
            SyntaxSearcher,
            fresh::{Mode, RefFormulaBuilder},
        },
    },
    terms::{
        BITE, EQ, FOBinder, Function, HAPPENS, LT, MACRO_FRAME, MITE, NONCE, PRED, RecFOFormula,
        formula_utils::pull_from_egraph,
    },
};
use bon::bon;
use egg::{Analysis, EGraph, Id};
use itertools::Itertools;
use logic_formula::{Formula, egg::SimplLang};
use std::borrow::Cow;
use utils::{ereturn_if, implvec};

#[derive(Debug, Clone)]
pub struct Nonce {
    content: RecFOFormula,
    name: Cow<'static, str>,
}

impl Nonce {
    pub fn new_from_args(head: Function, args: implvec!(RecFOFormula)) -> Self {
        Self::builder()
            .name(head.name.clone())
            .content(RecFOFormula::app(head, args.into_iter().collect()))
            .build()
    }

    pub fn as_recformula(&self) -> RecFOFormula {
        self.content.clone()
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
                tr!("builder mode {}", builder.borrow().mode());
                self.search_frame(egraph, &builder, time, ptcl);
                return;
            }

            // check is the nonce is there
            if head == &NONCE {
                tr!("found self ({})", self.name);
                let other = convert_id(egraph, current);
                builder.add_leaf(!EQ.rapp([other, NONCE.rapp([self.clone().as_recformula()])]));
                return; // <- no need to look further
            }
        }

        // main loop

        // fresh if indep of *one* of the e-class
        let builder = builder.add_node().or().build();
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
                    let builder = builder.add_node().and().build();
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
        let builder = builder.add_node().and().build();
        let (c, l, r) = args.iter().copied().collect_tuple().unwrap();

        self.search_egraph(egraph, builder.clone(), c, visited.clone());

        let c = convert_id(egraph, c);

        {
            // pos
            let builder = builder
                .add_node()
                .or()
                .forall()
                .condition(c.clone())
                .build();
            self.search_egraph(egraph, builder, l, visited.clone());
        }
        {
            // neg
            let builder = builder.add_node().or().forall().condition(!c).build();
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

                happend_cond & lt_cond
            };

            let builder =
                builder.add_node().mode(Mode::And)
                    .condition(condition)
                    .variables(vars.clone())
                    .sorts(id.signature.inputs_iter())
                    .quantifier(FOBinder::Forall).build();
            self.inner_search_recexpr(pbl, &builder, cond);
            self.inner_search_recexpr(pbl, &builder, msg);
        }
    }
}

impl SyntaxSearcher for Nonce {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("nonce")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        fun == &NONCE
    }

    fn process_instance<'a>(
        &self,
        _: &Problem,
        builder: &RefFormulaBuilder,
        fun: Function,
        args: implvec!(&'a [LangVar]),
    ) {
        assert_eq!(fun, NONCE);
        tr!("found nonce!");
        let arg = args.into_iter().next().expect("NONCE need a parameter");
        let content = !EQ.rapp([arg.into(), self.clone().as_recformula()]);
        builder.add_leaf(content);
    }
}

#[bon]
impl Nonce {
    #[builder(builder_type = NonceBuilder)]
    pub fn new(
        content: RecFOFormula,
        #[builder(into, default = format!("{content}"))] name: Cow<'static, str>,
    ) -> Self {
        Self { content, name }
    }
}

use nonce_builder::IsUnset as NonceBuilderIsUnset;
impl<S> NonceBuilder<S>
where
    S: nonce_builder::State,
{
    pub fn content_id<N: Analysis<Lang>>(
        self,
        egraph: &EGraph<Lang, N>,
        id: Id,
    ) -> NonceBuilder<SetContent<S>>
    where
        S::Content: NonceBuilderIsUnset,
    {
        let formula = RecFOFormula::try_from_id(egraph, id).unwrap();
        self.content(formula)
    }
}
