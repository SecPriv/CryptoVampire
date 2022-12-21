use crate::{
    formula::{
        builtins::{
            functions::{HAPPENS_NAME, LT_NAME},
            steps::INIT,
            types::STEP,
        },
        env::Environement,
    },
    smt::{macros::*, smt::Smt},
};

use super::Ctx;

pub(crate) fn ordering(
    _env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx<'_>,
) {
    let functions = &ctx.pbl.functions;
    let init = sfun!(functions.get(INIT.name()).unwrap().clone());
    let lt = functions.get(LT_NAME).unwrap().clone();
    let happens = functions.get(HAPPENS_NAME).unwrap().clone();

    assertions.push(Smt::AssertTh(sforall!(s!0:STEP; {
        sor!(
            sfun!(lt; init, s),
            seq!(init, s)
        )
    })));
    assertions.push(Smt::AssertTh(sforall!(s1!1:STEP, s2!2:STEP, s3!3:STEP ;{
        simplies!(
            sand!(
                sfun!(lt; s1, s2),
                sfun!(lt; s2, s3)
            ),
            sfun!(lt; s1, s3)
        )
    })));
    assertions.push(Smt::AssertTh(sforall!(s1!1:STEP, s2!2:STEP; {
        simplies!(
            sand!(
                sfun!(happens; s2),
                sfun!(lt; s1, s2)
            ),
            sfun!(happens; s1)
        )
    })));
    assertions.push(Smt::AssertTh(sforall!(s1!1:STEP, s2!2:STEP; {
        sor!(
            sfun!(lt; s1, s2),
            sfun!(lt; s2, s1),
            seq!(s1, s2),
            snot!(sfun!(happens; s1)),
            snot!(sfun!(happens; s2))
        )
    })));
    assertions.push(Smt::AssertTh(sfun!(happens; init)))
}
