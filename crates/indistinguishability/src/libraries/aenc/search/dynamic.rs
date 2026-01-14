use std::borrow::Cow;
use std::ops::ControlFlow;

use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use utils::ereturn_if;

use crate::libraries::AEnc;
use crate::libraries::aenc::vars::*;
use crate::libraries::utils::SyntaxSearcher;
use crate::libraries::utils::fresh::RefFormulaBuilder;
use crate::problem::{PAnalysis, RcRule};
use crate::runners::SmtRunner;
use crate::terms::{Formula, Function, NONCE};
use crate::{CVProgram, Lang, Problem, rexp};

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
    pk: Option<Function>,
    enc: Function,

    k: Formula,
}

#[derive(Debug, Clone)]
struct SearchO {
    #[allow(dead_code)]
    aenc: usize,

    pk: Option<Function>,
    dec: Function,
    enc: Function,

    k: Formula,
    // k2: RecFOFormula,
    // r: Formula,
}

impl SearchK {
    fn get_pk_enc(&self) -> &Function {
        self.pk.as_ref().unwrap_or(&self.enc)
    }

    fn is_senc(&self) -> bool {
        self.pk.is_none()
    }
}

impl SearchO {
    fn get_pk_enc(&self) -> &Function {
        self.pk.as_ref().unwrap_or(&self.enc)
    }
    fn is_senc(&self) -> bool {
        self.pk.is_none()
    }
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for SearchRule {
    fn name(&self) -> Cow<'_, str> {
        format!("enc vampire #{:}", self.aenc).into()
    }

    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        let Self {
            aenc,
            trigger_k,
            trigger_o,
            exec,
        } = self;
        let AEnc { pk, dec, enc, .. } = prgm.egraph().analysis.pbl().cryptography()[*aenc]
            .as_inner()
            .unwrap();
        let pk = pk.clone();
        let dec = dec.clone();
        let enc = enc.clone();

        if let Some(matches) = trigger_k.search_eclass(prgm.egraph(), goal) {
            assert!(!matches.substs.is_empty());
            tr!("matched trigger_k for {goal:}");
            for subst in matches.substs {
                let [k, t, h] = [K, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = SearchK {
                    aenc: *aenc,
                    pk: pk.clone(),
                    enc: enc.clone(),
                    k,
                }
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }

        if let Some(matches) = trigger_o.search_eclass(prgm.egraph(), goal) {
            assert!(!matches.substs.is_empty());
            tr!("matched trigger_o for {goal:}");
            for subst in matches.substs {
                let [k, t, h] = [K, T, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(P.as_egg()).unwrap();

                let result = (SearchO {
                    aenc: *aenc,
                    pk: pk.clone(),
                    dec: dec.clone(),
                    enc: enc.clone(),
                    k,
                })
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }
        Dependancy::impossible()
    }
}

impl crate::libraries::utils::SyntaxSearcher for SearchK {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search k enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, self.get_pk_enc()].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { pk: _, k, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k)));
        } else if fun == self.get_pk_enc() {
            tr!("found {}!", self.get_pk_enc());

            if self.is_senc() {
                assert_eq!(fun, &self.enc);

                let op = args.next().unwrap();
                let or = args.next().unwrap();
                let ok = args.next().unwrap();
                let builder = builder
                    .add_node()
                    .condition(rexp!((distinct (NONCE #k) #ok)))
                    .forall()
                    .build();

                self.inner_search_formula(pbl, &builder, op.clone());
                self.inner_search_formula(pbl, &builder, or.clone());
                self.inner_search_formula(pbl, &builder, ok.clone());
            } else {
                let ok = args.next().unwrap();
                let builder = builder
                    .add_node()
                    .condition(rexp!((distinct (NONCE #k) #ok)))
                    .forall()
                    .build();

                self.inner_search_formula(pbl, &builder, ok.clone());
            }
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}

impl crate::libraries::utils::SyntaxSearcher for SearchO {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search o enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, self.get_pk_enc(), &self.dec].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { pk: _, k, dec, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((distinct #arg #k)));
        } else if fun == self.get_pk_enc() {
            tr!("found {}!", self.get_pk_enc());

            if self.is_senc() {
                assert_eq!(fun, &self.enc);

                let op = args.next().unwrap();
                let or = args.next().unwrap();
                let ok = args.next().unwrap();
                let builder = builder
                    .add_node()
                    .condition(rexp!((distinct (NONCE #k) #ok)))
                    .forall()
                    .build();

                self.inner_search_formula(pbl, &builder, op.clone());
                self.inner_search_formula(pbl, &builder, or.clone());
                self.inner_search_formula(pbl, &builder, ok.clone());
            } else {
                let ok = args.next().unwrap();
                let builder = builder
                    .add_node()
                    .condition(rexp!((distinct (NONCE #k) #ok)))
                    .forall()
                    .build();

                self.inner_search_formula(pbl, &builder, ok.clone());
            }
        } else if fun == dec {
            tr!("found {dec}!");
            let (dm, dk) = args.collect_tuple().unwrap();

            self.inner_search_formula(pbl, builder, dm.clone());
            let builder = builder
                .add_node()
                .condition(rexp!((distinct #dk (NONCE #k) )))
                .build();
            self.inner_search_formula(pbl, &builder, dk.clone());
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}
