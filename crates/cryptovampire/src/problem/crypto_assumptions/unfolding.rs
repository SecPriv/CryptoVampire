use std::marker::PhantomData;

use itertools::chain;

use super::CryptoFlag;
use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::meq;
use crate::formula::function::Function;
use crate::formula::function::builtin::{
    CONDITION_MACRO, EXEC_MACRO, HAPPENS, LESS_THAN_EQ_STEP, MESSAGE_MACRO, PRED,
};
use crate::formula::sort::builtins::{CONDITION, MESSAGE, STEP};
use crate::formula::utils::Applicable;
use crate::problem::Problem;
use crate::{mforall, static_signature};

static_signature!((pub) UNFOLDING_MESSAGE_SIGNATURE: (STEP) -> MESSAGE);
static_signature!((pub) UNFOLDING_CONDITION_SIGNATURE: (STEP) -> CONDITION);
static_signature!((pub) UNFOLDING_EXEC_SIGNATURE: (STEP) -> CONDITION);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Unfolding<'bump> {
    // msg: Function<'bump>,
    // cond: Function<'bump>,
    // exec: Option<Function<'bump>>,
    flags: CryptoFlag,
    lt: PhantomData<Function<'bump>>,
}

impl<'bump> Unfolding<'bump> {
    pub fn new(flags: CryptoFlag) -> Self {
        Self {
            flags,
            lt: Default::default(),
        }
    }

    pub fn flags(&self) -> CryptoFlag {
        self.flags
    }

    pub fn exec(&self) -> Function<'bump> {
        *EXEC_MACRO
    }

    pub fn cond(&self) -> Function<'bump> {
        // self.cond
        *CONDITION_MACRO
    }

    pub fn msg(&self) -> Function<'bump> {
        // self.msg
        *MESSAGE_MACRO
    }

    pub fn use_recusive_def(&self) -> bool {
        // self.exec().is_some() &&
        self.flags().contains(CryptoFlag::RECURSIVE_EXEC)
    }

    pub fn use_direct_def(&self) -> bool {
        // self.exec().is_some()
        // &&
        self.flags().contains(CryptoFlag::DIRECT_EXEC)
            || !self.flags().contains(CryptoFlag::RECURSIVE_EXEC)
    }

    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        _: &mut Vec<Declaration<'bump>>,
        _: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        assertions.extend(chain! {
          [Axiom::Comment("unfolding".into())],
          self.generate_msg_cond(pbl), self.generate_exec(pbl)
        })
    }

    fn generate_exec<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = Axiom<'bump>> + 'a {
        let ev = pbl.evaluator();
        let step = STEP.as_sort();
        let exec = self.exec();

        {
            let recusive = self
                .use_recusive_def()
                .then(move || {
                    pbl.protocol().steps_without_init().iter().map(move |s| {
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
        }
        .map(Axiom::base)
    }

    fn generate_msg_cond<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
    ) -> impl Iterator<Item = Axiom<'bump>> + 'a {
        let ev = pbl.evaluator();
        pbl.protocol()
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
            .map(Axiom::base)
    }
}
