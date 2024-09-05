use derive_builder::Builder;
use itertools::chain;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::meq,
        function::{
            builtin::{HAPPENS, LESS_THAN_EQ_STEP, LESS_THAN_STEP, PRED},
            Function,
        },
        sort::builtins::STEP,
        utils::Applicable,
    },
    mforall,
    problem::Problem,
};

use super::CryptoFlag;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
pub struct Unfolding<'bump> {
    msg: Function<'bump>,
    cond: Function<'bump>,
    exec: Option<Function<'bump>>,
    #[builder(default)]
    flags: CryptoFlag,
}

impl<'bump> Unfolding<'bump> {
    pub fn flags(&self) -> CryptoFlag {
        self.flags
    }

    pub fn exec(&self) -> Option<Function<'bump>> {
        self.exec
    }

    pub fn cond(&self) -> Function<'bump> {
        self.cond
    }

    pub fn msg(&self) -> Function<'bump> {
        self.msg
    }

    pub fn use_recusive_def(&self) -> bool {
        self.exec().is_some() && self.flags().contains(CryptoFlag::RECURSIVE_EXEC)
    }
    pub fn use_direct_def(&self) -> bool {
        self.exec().is_some()
            && (self.flags().contains(CryptoFlag::DIRECT_EXEC)
                || !self.flags().contains(CryptoFlag::RECURSIVE_EXEC))
    }

    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        _: &mut Vec<Declaration<'bump>>,
        _: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let ev = pbl.evaluator();
        let step = STEP.as_sort();
        // message & condition
        let iter_msg_cond = pbl
            .protocol()
            .steps()
            .iter()
            .map(|s| {
                let indices = s.free_variables();
                let cond = s.condition_arc();
                let msg = s.message_arc();

                let tau = s.into_formula();

                mforall!(indices.iter().cloned(), {
                    HAPPENS.f([tau.clone()])
                        >> (meq(ev.eval(self.cond().f([tau.clone()])), ev.eval(cond))
                            & meq(ev.eval(self.msg().f([tau.clone()])), ev.eval(msg)))
                })
            })
            .map(Axiom::base);

        let iter_exec = self.exec().into_iter().flat_map(|exec| {
            let recusive = self
                .use_recusive_def()
                .then(move || {
                    pbl.protocol()
                        .steps_without_init()
                        .iter()
                        .map(move |s| {
                            let tau = s.into_formula();
                            mforall!(s.free_variables().iter().cloned(), {
                                HAPPENS.f([tau.clone()])
                                    >> meq(
                                        ev.eval(exec.f([tau.clone()])),
                                        ev.eval(self.cond().f([tau.clone()]))
                                            & ev.eval(exec.f([PRED.f([tau.clone()])])),
                                    )
                            })
                        })
                })
                .into_iter()
                .flatten();

            let direct = self.use_direct_def().then(|| {
                mforall!(s!1:step; {HAPPENS.f([s]) >>
                  meq(ev.eval(exec.f([s])),
                  mforall!(s2!2:step;
                      {LESS_THAN_EQ_STEP.f([s2, s]) >> ev.eval(self.cond().f([s]))}))})
            });

            chain!(
              [ev.eval(exec.f([pbl.protocol().init_step().into_formula()]))],
              recusive,
              direct
            )
        }).map(Axiom::base);

        assertions.extend(chain! {
          [Axiom::Comment("unfolding".into())],
          iter_msg_cond,
          iter_exec
        })
    }
}
