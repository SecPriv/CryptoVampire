use utils::{ereturn_if, ereturn_let};

use crate::libraries::Library;
use crate::libraries::utils::{INDEPEDANT_QUERY, SmtSink};
use crate::problem::cache::Context;
use crate::smt;
use crate::terms::HAPPENS;

pub struct CurrentStep;

impl Library for CurrentStep {
    fn add_smt<'a>(
        &self,
        pbl: &mut crate::Problem,
        context: &Context,
        sink: &mut impl SmtSink<'a>,
    ) {
        ereturn_if!(context.using_cache);
        ereturn_let!(let Some(cs) = pbl.current_step());

        let step_fun = pbl.get_step_name(cs.idx).unwrap();
        let args = cs.args.iter().map(|f| smt!(f));

        sink.assert_one(pbl, &INDEPEDANT_QUERY, smt!((HAPPENS (step_fun #args*))));
    }
}
