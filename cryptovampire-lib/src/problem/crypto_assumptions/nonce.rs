use crate::subterm::{kind::SubtermKindConstr, traits::DefaultAuxSubterm, Subterm};
use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::meq,
        function::inner::subterm::Subsubterm,
        sort::builtins::{MESSAGE, NAME},
    },
    mforall,
    problem::{generator::Generator, problem::Problem},
};

pub type SubtermNonce<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Nonce;

impl Nonce {
    pub fn generate<'bump>(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        assertions.push(Axiom::Comment("nonce".into()));
        let nonce_sort = NAME.clone();
        let message_sort = MESSAGE.clone();
        let ev = pbl.evaluator();
        let nc = pbl.name_caster();

        let kind = SubtermKindConstr::as_constr(pbl, env);
        let subterm = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_nonce"),
            &kind,
            DefaultAuxSubterm::new(nonce_sort),
            [],
            Default::default(),
            |rc| Subsubterm::Nonce(rc),
        );

        subterm.declare(env, pbl, declarations);

        if kind.is_vampire() {
        } else {
            assertions.extend(
                subterm
                    .generate_function_assertions_from_pbl(env, pbl)
                    .into_iter()
                    .chain(
                        subterm.not_of_sort(
                            env,
                            pbl.sorts()
                                .iter()
                                .filter(|&&s| !(s == nonce_sort || s.is_term_algebra()))
                                .cloned(),
                        ),
                    )
                    .map(|f| Axiom::base(f)),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, true)
                .map(|f| Axiom::base(f)),
        );

        assertions.extend(
            [
                mforall!(n1!0:nonce_sort, n2!1:nonce_sort; {
                    subterm.f_a(env, n1, n2) >> meq(n1, n2)
                })
                ,
            mforall!(n1!0:nonce_sort, n2!1:nonce_sort; {
                meq(ev.eval(nc.cast(message_sort, n1.clone())), ev.eval(nc.cast(message_sort, n2.clone())))
                    >> meq(n1, n2)
            })]
            .into_iter()
            .map(|f| Axiom::base(f)),
        );

        assertions.push(Axiom::Ground {
            sort: message_sort,
            formula: mforall!(n!0:nonce_sort, m!1:message_sort; {
                meq(ev.eval(nc.cast(message_sort, n.clone())),
                    ev.eval(m.clone())) >> subterm.f_a(env, n, m)
            }),
        })
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

impl<'bump> Generator<'bump> for Nonce {
    fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        self.generate(assertions, declarations, env, pbl)
    }
}
