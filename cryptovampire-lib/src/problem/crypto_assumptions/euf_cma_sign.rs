use std::{cell::RefCell, hash::Hash, sync::Arc};

use if_chain::if_chain;
use itertools::Itertools;
use static_init::dynamic;

use crate::subterm::{
    into_exist_formula,
    kind::SubtermKindConstr,
    traits::{DefaultAuxSubterm, SubtermAux, VarSubtermResult},
    Subterm,
};
use crate::{
    environement::{environement::Environement, traits::KnowsRealm},
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{forall, meq, ARichFormula, RichFormula},
        function::Function,
        function::{
            inner::subterm::Subsubterm, name_caster_collection::NameCasterCollection,
            signature::StaticSignature,
        },
        manipulation::OneVarSubst,
        sort::{
            builtins::{MESSAGE, NAME},
            Sort,
        },
        utils::formula_expander::DeeperKinds,
        variable::Variable,
    },
    mexists, mforall,
    problem::{generator::Generator, problem::Problem},
    static_signature,
};
use utils::arc_into_iter::ArcIntoIter;

pub type SubtermEufCmaSignMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermEufCmaSignKey<'bump> = Subterm<'bump, KeyAux<'bump>>;

static_signature!((pub) EUF_CMA_SIGN_SIGNATURE: (MESSAGE, MESSAGE) -> MESSAGE);
#[dynamic]
static EUF_CMA_VERIFY_SIGNATURE: StaticSignature<'static, 3> =
    super::EUF_CMA_VERIFY_SIGNATURE.clone();
static_signature!((pub) EUF_CMA_PK_SIGNATURE: (MESSAGE) -> MESSAGE);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EufCmaSign<'bump> {
    /// mac(Message, Key) -> Signature
    pub sign: Function<'bump>,
    /// verify(Signature, Message, Key) -> bool
    pub verify: Function<'bump>,
    /// verify(Key) -> pKey
    pub pk: Function<'bump>,
}

impl<'bump> EufCmaSign<'bump> {
    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let nonce_sort = NAME.clone();
        let message_sort = MESSAGE.clone();
        let ev = &pbl.evaluator;
        let nc = &pbl.name_caster;
        let kind = SubtermKindConstr::as_constr(pbl, env);

        let subterm_main = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_euf_cma_main"),
            &kind,
            DefaultAuxSubterm::new(message_sort),
            [],
            DeeperKinds::default(),
            |rc| Subsubterm::EufCmaSignMain(rc),
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_euf_cma_key"),
            &kind,
            KeyAux {
                euf_cma: *self,
                name_caster: Arc::clone(&pbl.name_caster),
            },
            [self.sign, self.pk],
            DeeperKinds::NO_MACROS,
            |rc| Subsubterm::EufCmaSignKey(rc),
        );

        if env.preprocess_instances() {
            assertions.extend(
                self.preprocess(env, pbl, subterm_main.as_ref(), subterm_key.as_ref())
                    .map(Axiom::base),
            )
        }

        if env.define_subterm() {
            define_subterms(
                env,
                pbl,
                assertions,
                declarations,
                &subterm_key,
                &subterm_main,
            );
        }

        if env.with_general_crypto_axiom() && env.define_subterm() {
            let max_var = pbl.max_var() + 1;
            let split = Function::new_spliting(env.container_full_life_time(), [nonce_sort]);
            declarations.push(Declaration::FreeFunction(split));

            assertions.push(Axiom::base({
                let k = Variable {
                    id: max_var,
                    sort: nonce_sort,
                };
                let k_f = k.into_aformula();
                let ors =
                    into_exist_formula(subterm_key.preprocess_whole_ptcl(env, &pbl.protocol, &k_f));

                forall([k], split.f_a([k_f]) >> ors)
            }));

            assertions.push(Axiom::Ground{
                sort: message_sort,
                formula: mforall!(m!1:message_sort, sigma!2:message_sort, k!3:nonce_sort; {
                    let k_f = nc.cast(message_sort, k);
                    ev.eval(self.verify.f([m.into(), sigma.into(), self.pk.f_a([ k_f.clone()])])) >>
                    mexists!(u!4:message_sort; {
                        meq(ev.eval(u.clone()), ev.eval(m)) &
                        (
                            subterm_main.f_a(env, self.sign.f_a([u.into(), k_f.clone()]), m.into()) |
                            subterm_main.f_a(env, self.sign.f_a([u.into(), k_f.clone()]), sigma.into()) |
                            subterm_key.f_a(env, k.clone(), m.clone()) |
                            subterm_key.f_a(env, k.clone(), sigma.clone()) |
                            split.f_a([k])
                        )
                    })
                }),
            })
        }
    }

    pub fn preprocess<'a>(
        &'a self,
        env: &impl KnowsRealm,
        pbl: &'a Problem<'bump>,
        subterm_main: &'a Subterm<'bump, impl SubtermAux<'bump>>,
        subterm_key: &'a Subterm<'bump, impl SubtermAux<'bump>>,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let max_var = pbl.max_var();
        // let pile1 = RefCell::new(Vec::new());
        let pile2 = RefCell::new(Vec::new());
        let realm = env.get_realm();
        let candidates = pbl
            .list_top_level_terms()
            .flat_map(|f| f.iter()) // sad...
            .filter_map(move |formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    if_chain! {
                        if fun == &self.verify;
                        if let RichFormula::Fun(mpk, args2) = args[2].as_ref();
                        if mpk == &self.pk;
                        if let RichFormula::Fun(nf, args3) = args2[0].as_ref();
                        if nf == pbl.name_caster.cast_function(&MESSAGE.as_sort()).unwrap();
                        then {
                            let [message, signature, key] =
                                [&args[1], &args[0], &args3[0]]
                                .map(|f| f.translate_vars(max_var).into_arc());

                            Some(EufCandidate {message, signature, key})
                        } else {None}
                    }
                }
                _ => None,
            })
            .unique()
            .filter_map(
                move |EufCandidate {
                          message,
                          signature,
                          key,
                      }| {
                    let array = [&message, &signature, &key];
                    let max_var = array
                        .iter()
                        .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                        .map(|Variable { id, .. }| id)
                        .max()
                        .unwrap_or(max_var)
                        + 1;
                    let free_vars = array
                        .iter()
                        .flat_map(|f| f.get_free_vars().into_iter())
                        // .cloned()
                        .unique();
                    let u_var = Variable {
                        id: max_var,
                        sort: MESSAGE.as_sort(),
                    };
                    let u_f = u_var.into_aformula();
                    let sign_of_u = self
                        .sign
                        .f_a([u_f, pbl.name_caster.cast(MESSAGE.as_sort(), &key)]);

                    let k_sc = subterm_key
                        .preprocess_terms(
                            &realm,
                            &pbl.protocol,
                            &key,
                            pbl.protocol
                                .list_top_level_terms_short_lifetime_and_bvars()
                                .chain([&message, &signature].map(|t| t.shallow_copy().into())),
                            false,
                            DeeperKinds::NO_MACROS,
                        )
                        .next()
                        .is_none();
                    if k_sc {
                        let mformula = {
                            let disjunction = subterm_main.preprocess_terms(
                                &realm,
                                &pbl.protocol,
                                &sign_of_u,
                                [&message, &signature].map(|x| x.shallow_copy().into()),
                                true,
                                DeeperKinds::all(),
                            );
                            into_exist_formula(disjunction)
                        };
                        if realm.is_symbolic_realm() {
                            Some(mforall!(free_vars, {
                                pbl.evaluator.eval(self.verify.f([
                                    signature.clone(),
                                    message.clone(),
                                    self.pk.f_a([
                                        pbl.name_caster.cast(MESSAGE.as_sort(), key.clone()),
                                    ]),
                                ])) >> mexists!([u_var], {
                                    meq(pbl.evaluator.eval(u_var), pbl.evaluator.eval(&message))
                                        & mformula
                                })
                            }))
                        } else {
                            Some(mforall!(free_vars, {
                                pbl.evaluator.eval(self.verify.f([
                                    signature.clone(),
                                    message.clone(),
                                    self.pk.f_a([
                                        pbl.name_caster.cast(MESSAGE.as_sort(), key.clone()),
                                    ]),
                                ])) >> mformula.apply_substitution2(&OneVarSubst {
                                    id: u_var.id,
                                    f: message.clone(),
                                })
                            }))
                        }

                        // Some(mforall!(free_vars, {
                        //     pbl.evaluator.eval(self.verify.f([
                        //         signature.clone(),
                        //         message.clone(),
                        //         self.pk.f_a([
                        //             pbl.name_caster.cast(MESSAGE.as_sort(), key.clone()),
                        //         ]),
                        //     ])) >> mexists!([u_var], { into_exist_formula(disjunction) })
                        // }))
                    } else {
                        None
                    }
                },
            );

        // [].into_iter()
        candidates
    }
}

#[allow(unused_labels)]
fn define_subterms<'bump>(
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    subterm_key: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
    subterm_main: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
) {
    if env.is_evaluated_realm() {
        return;
    }
    let _nonce_sort = NAME.clone();
    {
        let subterm = subterm_key.as_ref();
        subterm.declare(env, pbl, declarations);

        if subterm.kind().is_vampire() {
        } else {
            assertions.extend(
                itertools::chain!(
                    subterm
                        .generate_function_assertions_from_pbl(env, pbl)
                        .into_iter(),
                    subterm.not_of_sort_auto(env, pbl)
                )
                .map(|f| Axiom::base(f)),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, false)
                .map(|f| Axiom::base(f)),
        );
    }
    {
        let subterm = subterm_main.as_ref();
        subterm.declare(env, pbl, declarations);

        if subterm.kind().is_vampire() {
        } else {
            assertions.extend(
                itertools::chain!(
                    subterm
                        .generate_function_assertions_from_pbl(env, pbl)
                        .into_iter(),
                    subterm.not_of_sort_auto(env, pbl)
                )
                .map(|f| Axiom::base(f)),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, true)
                .map(|f| Axiom::base(f)),
        );
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct EufCandidate<'bump> {
    message: ARichFormula<'bump>,
    signature: ARichFormula<'bump>,
    key: ARichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    euf_cma: EufCmaSign<'bump>,
    name_caster: Arc<NameCasterCollection<'bump>>,
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn sort(&self) -> Sort<'bump> {
        NAME.clone()
    }

    fn var_eval_and_next(
        &self,
        m: &ARichFormula<'bump>,
    ) -> VarSubtermResult<'bump, Self::IntoIter> {
        let nexts = match m.as_ref() {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.euf_cma.sign;
                    if let RichFormula::Fun(nf, _args2) = args[1].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args2[0]])
                        break 'function [args[0].shallow_copy()].into() // can't be the subterm of another nonce
                    }
                }
                if_chain! {
                    if fun == &self.euf_cma.pk;
                    if let RichFormula::Fun(nf, _args2) = args[0].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        // break 'function VecRef::Vec(vec![&args[0], &args[1], &args2[0]])
                        break 'function [].into() // can't be the subterm of another nonce
                    }
                }
                ArcIntoIter::from(args)
            }
            _ => [].into(),
        };

        let m_sort = m.get_sort();

        VarSubtermResult {
            unified: m_sort.is_err() || self.sort() == m_sort.unwrap(),
            nexts,
        }
    }
}

impl<'bump> PartialOrd for KeyAux<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(&self, &other))
    }
}
impl<'bump> Ord for KeyAux<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.euf_cma, &other.euf_cma).then_with(|| {
            Ord::cmp(
                &Arc::as_ptr(&self.name_caster),
                &Arc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.euf_cma.hash(state);
        Arc::as_ptr(&self.name_caster).hash(state);
    }
}

impl<'bump> Generator<'bump> for EufCmaSign<'bump> {
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
