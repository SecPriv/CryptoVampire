use std::fmt::Display;
use std::hash::Hash;
use std::sync::Arc;

use derive_builder::Builder;
use if_chain::if_chain;
use itertools::{Itertools, chain};
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use static_init::dynamic;
use utils::utils::print_type;

use super::CryptoFlag;
use crate::environement::environement::Environement;
use crate::environement::traits::KnowsRealm;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{ARichFormula, RichFormula, forall, meq};
use crate::formula::function::Function;
use crate::formula::function::builtin::{EQUALITY, EQUALITY_TA, MESSAGE_TO_BITSTRING};
use crate::formula::function::inner::subterm::Subsubterm;
use crate::formula::function::signature::StaticSignature;
use crate::formula::manipulation::OneVarSubst;
use crate::formula::sort::builtins::{MESSAGE, NAME};
use crate::formula::utils::Applicable;
use crate::formula::utils::formula_expander::{NO_REC_MACRO, UnfoldFlags};
use crate::formula::variable::{IntoVariableIter, Variable, uvar};
use crate::problem::generator::Generator;
use crate::problem::problem::Problem;
use crate::subterm::kind::SubtermKindConstr;
use crate::subterm::traits::SubtermAux;
use crate::subterm::{Subterm, into_exist_formula};
use crate::{mexists, mforall, static_signature};

mod subterm;
pub use subterm::{KeyAux, UfCmaMainSubtAux};

pub type SubtermUfCmaMain<'bump> = Subterm<'bump, UfCmaMainSubtAux<'bump>>;
pub type SubtermUfCmaKey<'bump> = Subterm<'bump, KeyAux<'bump>>;

static_signature!((pub) UF_CMA_MAC_SIGNATURE: (MESSAGE, MESSAGE) -> MESSAGE);
#[dynamic]
#[allow(dead_code)]
pub static UF_CMA_VERIFY_SIGNATURE: StaticSignature<'static, 3> =
    super::EUF_CMA_VERIFY_SIGNATURE.clone();

/// Uf-Cma for MAC.
///
/// This contains `mac`, `verify`
///
///
/// See [paper](https://link.springer.com/chapter/10.1007/978-3-642-29011-4_22)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Builder)]
pub struct UfCma<'bump> {
    /// mac(Message, Key) -> Signature
    mac: Function<'bump>,
    /// verify(Signature, Message, Key) -> bool
    verify: Function<'bump>,
    #[builder(default)]
    flags: CryptoFlag,
}

impl<'bump> UfCma<'bump> {
    pub fn flags(&self) -> &CryptoFlag {
        &self.flags
    }

    /// verify(Signature, Message, Key) -> bool
    pub fn verify(&self) -> Function<'bump> {
        self.verify
    }

    /// mac(Message, Key) -> Signature
    pub fn mac(&self) -> Function<'bump> {
        self.mac
    }

    pub fn is_hmac(&self) -> bool {
        self.flags.contains(CryptoFlag::HMAC)
    }

    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        assertions.push(Axiom::Comment("uf-cma".into()));
        let nonce_sort = *NAME;
        let message_sort = *MESSAGE;
        let kind = SubtermKindConstr::as_constr(pbl, env);

        let subterm_main = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_uf_cma_main"),
            &kind,
            UfCmaMainSubtAux::new(*self),
            [self.mac, self.verify],
            UnfoldFlags::default(),
            Subsubterm::EufCmaMacMain,
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_uf_cma_key"),
            &kind,
            KeyAux::new(*self, pbl.owned_name_caster()),
            [self.mac, self.verify],
            NO_REC_MACRO,
            Subsubterm::EufCmaMacKey,
        );

        // base axiom
        assertions.push(Axiom::base(mforall!(m!1:message_sort, k!0:message_sort; {
            pbl.evaluator().eval(self.verify.f([self.mac.f([m, k]), m.into(), k.into()]))
        })));

        // preprocessing
        if env.preprocess_instances() {
            assertions.extend(
                self.preprocess(env, pbl, subterm_main.as_ref(), subterm_key.as_ref())
                    .map(Axiom::base),
            )
        }

        // subterm definition
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
                let formula = {
                    let iter = subterm_key.preprocess_whole_ptcl(env, pbl.protocol(), &k_f);
                    into_exist_formula(iter)
                };

                forall([k], split.f([k_f]) >> formula)
            }));

            // general crypto axiom
            assertions.push(Axiom::Ground{
                sort: message_sort,
                formula : mforall!(m!1:message_sort, sigma!2:message_sort, k!3:nonce_sort; {
                    let k_f = pbl.name_caster().cast(message_sort, k);
                    let ev = pbl.evaluator();
                    ev.eval(self.verify.f([m.into(), sigma.into(), k_f.clone()])) >>
                    mexists!(u!4:message_sort; {
                        meq(ev.eval(u), ev.eval(m)) &
                        (
                            subterm_main.f_a( env,self.mac.f([u.into(), k_f.clone()]), m.into()) |
                            subterm_main.f_a(env, self.mac.f([u.into(), k_f.clone()]), sigma.into()) |
                            subterm_key.f_a(env, k, m) |
                            subterm_key.f_a(env, k, sigma) |
                            split.f([k])
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
        trace!("max_var = {:?}", max_var);
        // let pile1 = RefCell::new(Vec::new());
        // let pile2 = RefCell::new(Vec::new());
        let realm = env.get_realm();
        let cast_messages = pbl.name_caster().cast_function(&MESSAGE.as_sort()).unwrap();
        trace!("looking for candidates");

        let tlt = pbl.list_top_level_terms().join("\n");
        trace!("top level terms: {tlt}");

        let candidates = pbl
            .list_top_level_terms()
            .flat_map(|f| f.iter_with(AllTermsIterator, ())) // sad...
            .flat_map(move |formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    trace!("{:}", formula.as_ref());
                    chain![
                        // <-- using chain to not miss situations like hash(x, y) = hash(w, z)
                        if_chain! { // verify
                            if fun == &self.verify;
                            if let [sign, mess, key] = args.as_ref();
                            if let RichFormula::Fun(f, args) = key.as_ref();
                            if f == cast_messages;
                            if let [key] = args.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // hash(m, k) = sigma, with no evaluate (hmac)
                            if self.is_hmac();
                            // if realm.is_evaluated();
                            if fun == &EQUALITY.clone();
                            if let [hmaced, sign] = args.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // sigma = hash(m, k), with no evaluate
                            if self.is_hmac();
                            // if realm.is_evaluated();
                            if fun == &EQUALITY.clone();
                            if let [sign, hmaced] = args.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // |hash(m, k)| = |sigma|
                            if self.is_hmac();
                            // if realm.is_symbolic();
                            if fun == &EQUALITY.clone();
                            if let [e_hmaced, e_sign] = args.as_ref();
                            if let RichFormula::Fun(eval1, args_e_sign) = e_sign.as_ref();
                            if let RichFormula::Fun(eval2, args_e_hmaced) = e_hmaced.as_ref();
                            if (eval1 == eval2) && (eval1 == &MESSAGE_TO_BITSTRING.clone());
                            if let [hmaced] = args_e_hmaced.as_ref();
                            if let [sign] = args_e_sign.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // |sigma| = |hash(m, k)|
                            if self.is_hmac();
                            // if realm.is_symbolic();
                            if fun == &EQUALITY.clone();
                            if let [e_sign, e_hmaced] = args.as_ref();
                            if let RichFormula::Fun(eval1, args_e_sign) = e_sign.as_ref();
                            if let RichFormula::Fun(eval2, args_e_hmaced) = e_hmaced.as_ref();
                            if (eval1 == eval2) && (eval1 == &MESSAGE_TO_BITSTRING.clone());
                            if let [hmaced] = args_e_hmaced.as_ref();
                            if let [sign] = args_e_sign.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // | ... hash(m, k) === sigma ... |
                            if self.is_hmac();
                            // if realm.is_symbolic();
                            if fun == &EQUALITY_TA.clone();
                            if let [hmaced, sign] = args.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                        if_chain! { // | .... sigma = hash(m, k) ... |, with no evaluate
                            if self.is_hmac();
                            // if realm.is_symbolic();
                            if fun == &EQUALITY_TA.clone();
                            if let [sign, hmaced] = args.as_ref();
                            if let RichFormula::Fun(hmac, argshash) = hmaced.as_ref();
                            if hmac == &self.mac;
                            if let [mess, key] = argshash.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                Some(prepare_candidate(max_var, mess, sign, key))
                            } else {None}
                        },
                    ]
                    .collect_vec()
                }
                _ => vec![],
            })
            .unique()
            .inspect(|candidate| trace!("uf-cma (preprocessing): found candidate:\n{candidate}"))
            .filter_map(
                move |UfCmaCandidate {
                          message,
                          signature,
                          key,
                      }| {
                    let array = [&message, &signature, &key];
                    // let max_var = array
                    //     .iter()
                    //     .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                    //     .map(|Variable { id, .. }| id)
                    //     .max()
                    //     .unwrap_or(max_var)
                    //     + 1;
                    let max_var = array.iter().copied().max_var_or_max(max_var);
                    let free_vars = array
                        .iter()
                        .flat_map(|f| (*f).free_vars_iter())
                        // .cloned()
                        .unique();
                    let u_var = Variable {
                        id: max_var,
                        sort: MESSAGE.as_sort(),
                    };
                    // let u_f = u_var.into_aformula();

                    let h_of_u = self.mac.f([
                        u_var.into(),
                        pbl.name_caster().cast(MESSAGE.as_sort(), &key),
                    ]);

                    let k_sc = subterm_key
                        .preprocess_terms(
                            &realm,
                            pbl.protocol(),
                            &key,
                            pbl.protocol()
                                .list_top_level_terms_short_lifetime_and_bvars()
                                .chain([&message, &signature].map(|t| t.shallow_copy().into())),
                            false,
                            NO_REC_MACRO,
                        )
                        .next()
                        .is_none();
                    if k_sc {
                        let mformula = {
                            let iter = subterm_main.preprocess_terms(
                                &realm,
                                pbl.protocol(),
                                &h_of_u,
                                [&message, &signature].map(|f| f.shallow_copy().into()),
                                true,
                                UnfoldFlags::all(),
                            );
                            into_exist_formula(iter)
                        };

                        let app_key = pbl.name_caster().cast(MESSAGE.as_sort(), key.clone());
                        if realm.is_symbolic_realm() {
                            Some(mforall!(free_vars, {
                                // pbl.evaluator().eval(self.verify.apply([
                                //     signature.clone(),
                                //     message.clone(),
                                //     pbl.name_caster().cast(MESSAGE.as_sort(), key.clone()),
                                // ]))
                                self.apply_eval_verify(
                                    pbl,
                                    signature.clone(),
                                    message.clone(),
                                    app_key,
                                ) >> mexists!([u_var], {
                                    meq(pbl.evaluator().eval(u_var), pbl.evaluator().eval(&message))
                                        & mformula
                                })
                            }))
                        } else {
                            Some(mforall!(free_vars, {
                                // pbl.evaluator().eval(self.verify.apply([
                                //     signature.clone(),
                                //     message.clone(),
                                //     pbl.name_caster().cast(MESSAGE.as_sort(), key.clone()),
                                // ]))
                                self.apply_eval_verify(
                                    pbl,
                                    signature.clone(),
                                    message.clone(),
                                    app_key,
                                ) >> mformula.apply_substitution2(&OneVarSubst {
                                    id: u_var.id,
                                    f: message.clone(),
                                })
                            }))
                        }
                    } else {
                        None
                    }
                },
            );

        // [].into_iter()
        candidates
    }

    pub fn apply_eval_verify(
        &self,
        pbl: &Problem<'bump>,
        signature: ARichFormula<'bump>,
        message: ARichFormula<'bump>,
        key: ARichFormula<'bump>,
    ) -> ARichFormula<'bump> {
        let ev = pbl.evaluator();
        if self.is_hmac() {
            meq(ev.eval(signature), ev.eval(self.mac.f([message, key])))
        } else {
            ev.eval(self.verify.f([signature, message, key]))
        }
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
    // if you're in the evaluated realm we don't need to define anything because it wouldn't be sound
    if env.is_evaluated_realm() {
        return;
    }

    let _nonce_sort = *NAME;
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
                .map(Axiom::base),
            );
        }
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, false)
                .map(Axiom::base),
        );
    }

    {
        let subterm = subterm_main.as_ref();
        subterm.declare(env, pbl, declarations);

        trace!(".");

        if subterm.kind().is_vampire() {
        } else {
            assertions.extend(
                itertools::chain!(
                    subterm
                        .generate_function_assertions_from_pbl(env, pbl)
                        .into_iter(),
                    subterm.not_of_sort_auto(env, pbl)
                )
                .map(Axiom::base),
            );
        }
        trace!("subterm type: {}", print_type(subterm));
        assertions.extend(
            subterm
                .preprocess_special_assertion_from_pbl(env, pbl, true)
                .map(Axiom::base),
        );
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct UfCmaCandidate<'bump> {
    message: ARichFormula<'bump>,
    signature: ARichFormula<'bump>,
    key: ARichFormula<'bump>,
}

impl<'bump> Display for UfCmaCandidate<'bump> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let UfCmaCandidate {
            message,
            signature,
            key,
        } = self;
        write!(f, "sign({message}, {key}) = {signature}")
    }
}

impl<'bump> Generator<'bump> for UfCma<'bump> {
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

fn prepare_candidate<'bump>(
    max_var: uvar,
    message: &ARichFormula<'bump>,
    signature: &ARichFormula<'bump>,
    key: &ARichFormula<'bump>,
) -> UfCmaCandidate<'bump> {
    trace!(
        "candidate found as m={:}, s={:}, k={:}",
        message, signature, key
    );
    let [message, signature, key] =
        [message, signature, key].map(|f| f.translate_vars(max_var).into_arc());
    trace!(
        "after var remmap m={:}, s={:}, k={:}",
        &message, &signature, &key
    );
    UfCmaCandidate {
        message,
        signature,
        key,
    }
}

impl<'bump> UfCmaBuilder<'bump> {
    #[allow(dead_code)]
    pub fn hmac(&mut self, v: bool) -> &mut Self {
        if v {
            let tmp = self
                .flags
                .map(|f| f | CryptoFlag::HMAC)
                .unwrap_or(CryptoFlag::HMAC);
            self.flags = Some(tmp);
        }
        self
    }
}
