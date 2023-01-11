use crate::{
    formula::{
        builtins::{
            functions::{HAPPENS_NAME, LT_NAME},
            types::STEP,
        },
        env::Environement,
    },
    smt::{
        macros::*,
        smt::{Smt, SmtFormula},
    },
};

use super::Ctx;

pub(crate) fn ordering(
    env: &Environement,
    assertions: &mut Vec<Smt>,
    _declarations: &mut Vec<Smt>,
    ctx: &Ctx,
) {
    // let functions = &ctx.pbl.functions;
    let init = sfun!(ctx.pbl.get_init_step_function().clone());
    let lt = env.get_f(LT_NAME).unwrap().clone();
    let happens = env.get_f(HAPPENS_NAME).unwrap().clone();
    let step = STEP(env);

    let mut assert_tmp = Vec::new();

    assertions.push(Smt::Comment(format!("ordering")));

    assert_tmp.push(sforall!(s!0:step; {
        sor!(
            sfun!(lt; init, s),
            seq!(init, s)
        )
    }));
    assert_tmp.push(sforall!(s!1:step; {
        simplies!(ctx.env();
            sfun!(lt; s.clone(), s.clone()),
            seq!(init, s)
        )
    }));
    assert_tmp.push(sforall!(s1!1:step, s2!2:step, s3!3:step ;{
        simplies!(env;
            sand!(
                sfun!(lt; s1, s2),
                sfun!(lt; s2, s3)
            ),
            sfun!(lt; s1, s3)
        )
    }));
    assert_tmp.push(sforall!(s1!1:step, s2!2:step; {
        simplies!(env;
            sand!(
                sfun!(happens; s2),
                sfun!(lt; s1, s2)
            ),
            sfun!(happens; s1)
        )
    }));
    assert_tmp.push(sforall!(s1!1:step, s2!2:step; {
        sor!(
            sfun!(lt; s1, s2),
            sfun!(lt; s2, s1),
            seq!(s1, s2),
            snot!(env; sfun!(happens; s1)),
            snot!(env; sfun!(happens; s2))
        )
    }));
    assert_tmp.push(sfun!(happens; init));

    if ctx.env().use_assert_theory() {
        assertions.extend(assert_tmp.into_iter().map(Smt::AssertTh))
    } else {
        assertions.extend(assert_tmp.into_iter().map(Smt::Assert))
    };

    assertions.extend(
        ctx.pbl
            .order
            .iter()
            .map(|f| Smt::Assert(SmtFormula::from(f))),
    )
}
