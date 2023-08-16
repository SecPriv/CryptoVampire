use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::meq,
        function::builtin::{HAPPENS, LESS_THAN_STEP},
        sort::builtins::STEP,
        variable::Variable,
    },
    mforall,
    problem::problem::Problem,
};

pub fn generate<'bump>(
    assertions: &mut Vec<Axiom<'bump>>,
    _: &mut Vec<Declaration<'bump>>,
    _: &Environement<'bump>,
    pbl: &Problem<'bump>,
) {
    assertions.push(Axiom::Comment("ordering".into()));

    let lt = LESS_THAN_STEP.clone();
    let happens = HAPPENS.clone();
    let step = STEP.clone();
    let init = pbl
        .protocol
        .init_step()
        .function()
        .f_a::<Variable<'bump>>([]);

    assertions.extend(
        [
            mforall!(s!0:step; {
                lt.f_a([init.clone(), s.into()]) | meq(init.clone(), s)
            }),
            mforall!(s!0:step; {
                lt.f_a([s.clone(), s.clone()]) >> meq(s.clone(), init.clone())
            }),
            mforall!(s1!1:step, s2!2:step, s3!3:step; {
                (
                    lt.f_a([s1.clone(), s2.clone()]) &
                    lt.f_a([s2.clone(), s3.clone()])
                ) >> lt.f_a([s1, s3])
            }),
            mforall!(s1!1:step, s2!2:step; {
                (happens.f([s2.clone()]) & lt.f([s1.clone(), s2.clone()])) >> happens.f([s1])
            }),
            mforall!(s1!1:step, s2!2:step; {
                lt.f_a([s1.clone(), s2.clone()]) |
                lt.f_a([s2.clone(), s1.clone()]) |
                meq(s1.clone(), s2.clone()) |
                (!happens.f_a([s1.clone()])) |
                (!happens.f_a([s2.clone()]))
            }),
            happens.f_a([init.clone()]),
        ]
        .into_iter()
        .map(Axiom::theory)
        .chain(pbl.protocol.ordering().iter().cloned().map(Axiom::base)),
    );
}
