use crate::environement::environement::Environement;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::meq;
use crate::formula::function::inner::subterm::Subsubterm;
use crate::formula::sort::builtins::{MESSAGE, NAME};
use crate::mforall;
use crate::problem::generator::Generator;
use crate::problem::problem::Problem;
use crate::subterm::Subterm;
use crate::subterm::kind::SubtermKindConstr;
use crate::subterm::traits::DefaultAuxSubterm;

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
        let nonce_sort = *NAME;
        let message_sort = *MESSAGE;
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
            Subsubterm::Nonce,
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
                    .map(Axiom::base),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, true)
                .map(Axiom::base),
        );

        assertions.extend(
            [
                mforall!(n1!0:nonce_sort, n2!1:nonce_sort; {
                    subterm.f_a(env, n1, n2) >> meq(n1, n2)
                }),
                mforall!(n1!0:nonce_sort, n2!1:nonce_sort; {
                    meq(ev.eval(nc.cast(message_sort, n1)), ev.eval(nc.cast(message_sort, n2)))
                        >> meq(n1, n2)
                }),
            ]
            .into_iter()
            .map(Axiom::base),
        );

        assertions.push(Axiom::Ground {
            sort: message_sort,
            formula: mforall!(n!0:nonce_sort, m!1:message_sort; {
                meq(ev.eval(nc.cast(message_sort, n)),
                    ev.eval(m)) >> subterm.f_a(env, n, m)
            }),
        })
    }
}

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
