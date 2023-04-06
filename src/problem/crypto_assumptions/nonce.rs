use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        sort::builtins::NONCE,
    },
    problem::{
        problem::Problem,
        subterm::{traits::DefaultAuxSubterm, Subterm},
    },
};

pub type SubtermNonce<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nonce;

impl Nonce {
    pub fn generate<'bump>(
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let subterm = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_nonce"),
            env.into(),
            DefaultAuxSubterm::new(NONCE.clone()),
            [],
            |rc| crate::formula::function::subterm::Subsubterm::Nonce(rc),
        );
    }
}

// pub(crate) fn generate(assertions: &mut Vec<Smt>, declarations: &mut Vec<Smt>, ctx: &mut Ctx) {
//     // if ctx.env().no_subterm() {
//     //     return;
//     // }

//     // let eval_msg = get_eval_msg(ctx.env());
//     let evaluator = Evaluator::new(ctx.env()).unwrap();
//     let nonce = NONCE_MSG(ctx.env()).clone();
//     let nonce_sort = NONCE(ctx.env()).clone();
//     let msg = MSG(ctx.env()).clone();

//     let subt_main = Subterm::new_and_init(
//         assertions,
//         declarations,
//         ctx,
//         "sbt$nonce_main".to_owned(),
//         nonce_sort.clone(),
//         [],
//         Default::default(),
//         DefaultBuilder(),
//     );

//     // assertions.push(Smt::Assert(sforall!(n!0:nonce_sort, m!1:msg;{
//     //     simplies!(ctx.env();
//     //         seq!(sfun!(eval_msg; sfun!(nonce; n.clone())), sfun!(eval_msg; m.clone())),
//     //         subt_main.f(ctx, n.clone(), m.clone(), &msg)
//     //     )
//     // })))

//     assertions.push(Smt::Assert(ctx.forallff(
//         [(0, &nonce_sort), (1, &msg)],
//         |[n, m]: [SmtFormula; 2]| {
//             ctx.impliesf(
//                 ctx.eqf(
//                     evaluator.msg(ctx, nonce.cf(ctx, [n.clone()])),
//                     evaluator.msg(ctx, m.clone()),
//                 ),
//                 subt_main.f(ctx, n, m, &msg),
//             )
//         },
//     )))
// }
