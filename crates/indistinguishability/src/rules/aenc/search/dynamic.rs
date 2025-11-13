use crate::{
    Lang, Problem,
    problem::PAnalysis,
    rexp,
    rules::{
        AEnc,
        aenc::vars::*,
        utils::{SyntaxSearcher, fresh::RefFormulaBuilder},
    },
    runners::SmtRunner,
    terms::{Function, NONCE, Formula},
};
use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use std::{borrow::Cow, ops::ControlFlow};
use utils::ereturn_if;

#[derive(Debug, Clone, Builder)]
pub struct SearchRule {
    aenc: usize,
    #[builder(into)]
    trigger_k: Pattern<Lang>,
    #[builder(into)]
    trigger_o: Pattern<Lang>,
    exec: SmtRunner,
}

#[derive(Debug, Clone)]
struct SearchK {
    #[allow(dead_code)]
    aenc: usize,
    pk: Function,
    k: Formula,
    dec: Function,
}

#[derive(Debug, Clone)]
struct SearchO {
    #[allow(dead_code)]
    aenc: usize,

    pk: Function,

    k: Formula,
    // k2: RecFOFormula,
    r: Formula,
}

impl<'a> Rule<Lang, PAnalysis<'a>> for SearchRule {
    fn name(&self) -> Cow<'_, str> {
        format!("enc vampire #{:}", self.aenc).into()
    }

    fn search(&self, prgm: &mut golgge::Program<Lang, PAnalysis<'a>>, goal: Id) -> Dependancy {
        let Self {
            aenc,
            trigger_k,
            trigger_o,
            exec,
        } = self;
        let AEnc { pk, dec, .. } = prgm.egraph().analysis.pbl().cryptography()[*aenc]
            .as_aenc()
            .unwrap();
        let pk = pk.clone();
        let dec = dec.clone();

        if let Some(matches) = trigger_k.search_eclass(prgm.egraph(), goal) {
            for subst in matches.substs {
                let [k, t, h] = [K, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = SearchK {
                    aenc: *aenc,
                    pk: pk.clone(),
                    dec: dec.clone(),
                    k,
                }
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }

        if let Some(matches) = trigger_o.search_eclass(prgm.egraph(), goal) {
            for subst in matches.substs {
                let [k, r, t, h] = [K, R, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = (SearchO {
                    aenc: *aenc,
                    pk: pk.clone(),
                    k,
                    r,
                })
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }
        Dependancy::impossible()
    }
}

impl crate::rules::utils::SyntaxSearcher for SearchK {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search k enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, &self.pk, &self.dec].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { pk, k, dec, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k)));
        } else if fun == pk {
            tr!("found {pk}!");

            let ok = args.next().unwrap();
            let builder = builder
                .add_node()
                .condition(rexp!((distinct (NONCE #k) #ok)))
                .forall()
                .build();

            self.inner_search_formula(pbl, &builder, ok.clone());
        } else if fun == dec {
            tr!("found {dec}!");
            let (dm, dk) = args.collect_tuple().unwrap();

            self.inner_search_formula(pbl, builder, dm.clone());
            let builder = builder
                .add_node()
                .condition(rexp!((distinct #dk (NONCE #k) )))
                .forall()
                .build();
            self.inner_search_formula(pbl, &builder, dk.clone());
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}

impl crate::rules::utils::SyntaxSearcher for SearchO {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search o enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, &self.pk].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { pk, r, k, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k #r)));
        } else if fun == pk {
            tr!("found {pk}!");

            let arg = args.next().unwrap();
            let builder = builder
                .add_node()
                .condition(rexp!((distinct (NONCE #k)  #arg)))
                .forall()
                .build();

            self.inner_search_formula(pbl, &builder, arg.clone());
        }
        // else  if fun == dec {
        //     tr!("found {dec}!");
        //     let (dm, dk) = args.collect_tuple().unwrap();

        //     self.inner_search_formula(pbl, builder, dm.clone());
        //     let builder = builder
        //         .add_node()
        //         .condition(rexp!((distinct #dk (NONCE #k) )))
        //         .build();
        //     self.inner_search_formula(pbl, &builder, dk.clone());
        // }
        else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}
