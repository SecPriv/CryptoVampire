use utils::{ereturn_if, ereturn_let};

use crate::{libraries::{Library, utils::{ INDEPEDANT_QUERY, SmtSink}}, problem::data::Context, smt, terms::HAPPENS};

pub struct CurrentStep;

impl Library for CurrentStep {
  fn add_smt(&self, pbl: &mut crate::Problem, context: &Context,  sink: &mut impl SmtSink) {
      ereturn_if!(context.using_cache);
      ereturn_let!(let Some(cs) = pbl.current_step());

      let step_fun = pbl.get_step_name(cs.idx).unwrap();
      let args = cs.args.iter().map(|f| smt!(f));

      sink.assert_one(pbl, &INDEPEDANT_QUERY, smt!((HAPPENS (step_fun #args*))));
  }
}