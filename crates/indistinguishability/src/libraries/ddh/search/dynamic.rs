use std::borrow::Cow;
use std::ops::ControlFlow;

use bon::Builder;
use egg::{Id, Pattern, Searcher};
use golgge::{Dependancy, Rule};
use itertools::Itertools;
use utils::ereturn_if;

use crate::libraries::DDH;
use crate::libraries::ddh::vars::*;
use crate::libraries::utils::SyntaxSearcher;
use crate::libraries::utils::fresh::RefFormulaBuilder;
use crate::problem::{PAnalysis, RcRule};
use crate::runners::SmtRunner;
use crate::terms::{Formula, Function, NONCE};
use crate::{CVProgram, Lang, Problem, rexp};

#[derive(Debug, Clone, Builder)]
pub struct SearchRule {
    ddh: usize,
    #[builder(into)]
    trigger: Pattern<Lang>,
    exec: SmtRunner,
}

#[derive(Debug, Clone)]
struct SearchK {
    #[allow(dead_code)]
    ddh: usize,
    g: Function,
    exp: Function,
    a: Formula,
    b: Formula,
}

impl<'a> Rule<Lang, PAnalysis<'a>, RcRule> for SearchRule {
    fn name(&self) -> Cow<'_, str> {
        format!("enc vampire #{:}", self.ddh).into()
    }

    fn search(&self, prgm: &mut CVProgram<'a>, goal: Id) -> Dependancy {
        let Self { ddh, trigger, exec } = self;
        let DDH { g, exp, .. } = prgm.egraph().analysis.pbl().cryptography()[*ddh]
            .as_inner()
            .unwrap();
        let g = g.clone();
        let exp = exp.clone();

        if let Some(matches) = trigger.search_eclass(prgm.egraph(), goal) {
            for subst in matches.substs {
                let [a, b, t, h] = [NA, NB, TIME, H]
                    .map(|v| subst.get(v.as_egg()).unwrap())
                    .map(|id| Formula::try_from_id(prgm.egraph(), *id).unwrap());
                let p = *subst.get(PTCL.as_egg()).unwrap();

                let result = SearchK {
                    ddh: *ddh,
                    g: g.clone(),
                    exp: exp.clone(),
                    a,
                    b,
                }
                .search_id_timepoint(prgm, exec, p, t, h)
                .unwrap();
                ereturn_if!(result, Dependancy::axiom());
            }
        }
        Dependancy::impossible()
    }
}

impl SyntaxSearcher for SearchK {
    fn debug_name<'a>(&'a self) -> std::borrow::Cow<'a, str> {
        Cow::Borrowed("search k enc")
    }

    fn is_instance(&self, _: &Problem, fun: &Function) -> bool {
        [&NONCE, &self.exp].contains(&fun)
    }

    fn process_instance(
        &self,
        pbl: &Problem,
        builder: &RefFormulaBuilder,
        fun: &Function,
        args: &[Formula],
    ) -> ControlFlow<()> {
        let Self { a, b, exp, .. } = self;
        let mut args = args.iter();
        if fun == &NONCE {
            tr!("found key!");
            let arg = args.next().expect("NONCE needs a parameter");
            builder.add_leaf(rexp!((and (distinct #arg #a) (distinct #arg #b))));
        } else if fun == exp {
            tr!("found {exp}!");

            let (base, exponent) = args.collect_tuple().unwrap();
            let mut pile = Vec::new();
            self.unpile_exp(&mut pile, base, exponent);

            tr!("pile:\n\t[{}\n]", pile.iter().join(",\n"));

            let builder = if pile.is_empty() {
                Cow::Borrowed(builder)
            } else {
                let [na, nb] = [a, b].map(|x| {
                    let args = pile.iter().map(|&e| rexp!((distinct #e (NONCE #x))));
                    rexp!((and #args*))
                });
                {
                    let builder = builder.add_node().or().build();
                    builder.add_leaf(na.clone());
                    builder.add_leaf(nb.clone());
                }
                Cow::Owned(
                    builder
                        .add_node()
                        .condition(rexp!((and #na #nb)))
                        .forall()
                        .build(),
                )
            };

            self.inner_search_formula(pbl, &builder, base.clone());
            self.inner_search_formula(pbl, &builder, exponent.clone());
        } else {
            assert!(!self.is_instance(pbl, fun));
            unreachable!()
        }
        ControlFlow::Break(())
    }
}

impl SearchK {
    /// turns `(((g^a)^b)^c)^d` into `[d, b, a, c]` by setting `pile`. Sets
    /// `pile` to `[]` if it doesn't have the right shape
    ///
    /// It expect `base=(((g^a)^b)^c)` and `exponent=d`
    fn unpile_exp<'a>(
        &self,
        pile: &mut Vec<&'a Formula>,
        base: &'a Formula,
        exponent: &'a Formula,
    ) {
        pile.push(exponent);
        match base {
            Formula::App { head, args } if head == &self.exp => {
                self.unpile_exp(pile, &args[0], &args[1]);
            }
            Formula::App { head, .. } if head == &self.g => {}
            _ => {
                pile.clear();
            }
        }
    }
}
