use std::hash::Hash;
use std::sync::Arc;

use if_chain::if_chain;
use itertools::Itertools;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use utils::arc_into_iter::ArcIntoIter;

use crate::environement::environement::Environement;
use crate::environement::traits::KnowsRealm;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{ARichFormula, RichFormula, forall, meq};
use crate::formula::function::Function;
use crate::formula::function::inner::subterm::Subsubterm;
use crate::formula::function::name_caster_collection::NameCasterCollection;
use crate::formula::manipulation::OneVarSubst;
use crate::formula::sort::Sort;
use crate::formula::sort::builtins::{CONDITION, MESSAGE, NAME};
use crate::formula::utils::Applicable;
use crate::formula::utils::formula_expander::{NO_REC_MACRO, UnfoldFlags};
use crate::formula::variable::{IntoVariableIter, Variable};
use crate::problem::generator::Generator;
use crate::problem::problem::Problem;
use crate::subterm::kind::SubtermKindConstr;
use crate::subterm::traits::{DefaultAuxSubterm, SubtermAux, VarSubtermResult};
use crate::subterm::{Subterm, into_exist_formula};
use crate::{mexists, mforall, static_signature};

pub type SubtermEufCmaSignMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermEufCmaSignKey<'bump> = Subterm<'bump, KeyAux<'bump>>;

static_signature!((pub) EUF_CMA_SIGN_SIGNATURE: (MESSAGE, MESSAGE) -> MESSAGE);
static_signature!((pub) EUF_CMA_VERIFY_SIGNATURE: (MESSAGE, MESSAGE, MESSAGE) -> CONDITION);
static_signature!((pub) EUF_CMA_PK_SIGNATURE: (MESSAGE) -> MESSAGE);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EufCma<'bump> {
    /// mac(Message, Key) -> Signature
    pub sign: Function<'bump>,
    /// verify(Signature, Message, Key) -> bool
    pub verify: Function<'bump>,
    /// verify(Key) -> pKey
    pub pk: Function<'bump>,
}

impl<'bump> EufCma<'bump> {
    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        assertions.push(Axiom::Comment("euf-cma sign".into()));
        let nonce_sort = *NAME;
        let message_sort = *MESSAGE;
        let kind = SubtermKindConstr::as_constr(pbl, env);

        let subterm_main = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_euf_cma_main"),
            &kind,
            DefaultAuxSubterm::new(message_sort),
            [],
            UnfoldFlags::default(),
            Subsubterm::EufCmaSignMain,
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container.find_free_function_name("subterm_euf_cma_key"),
            &kind,
            KeyAux {
                euf_cma: *self,
                name_caster: pbl.owned_name_caster(),
            },
            [self.sign, self.pk],
            NO_REC_MACRO,
            Subsubterm::EufCmaSignKey,
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
                let ors = into_exist_formula(subterm_key.preprocess_whole_ptcl(
                    env,
                    pbl.protocol(),
                    &k_f,
                ));

                forall([k], split.f([k_f]) >> ors)
            }));

            assertions.push(Axiom::Ground{
                sort: message_sort,
                formula: mforall!(m!1:message_sort, sigma!2:message_sort, k!3:nonce_sort; {
                    let k_f = pbl.name_caster().cast(message_sort, k);
                    let ev = pbl.evaluator();
                    ev.eval(self.verify.apply([m.into(), sigma.into(), self.pk.f([ k_f.clone()])])) >>
                    mexists!(u!4:message_sort; {
                        meq(ev.eval(u), ev.eval(m)) &
                        (
                            subterm_main.f_a(env, self.sign.f([u.into(), k_f.clone()]), m.into()) |
                            subterm_main.f_a(env, self.sign.f([u.into(), k_f.clone()]), sigma.into()) |
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
        let realm = env.get_realm();

        // This list the formulas to add to the smt files
        let candidates = pbl
            // loops through all terms/formulas that appears in the problem
            .list_top_level_terms()
            // loop through all subterms in the problem
            .flat_map(|f| f.iter_with(AllTermsIterator, ())) // sad...
            // now the iterator will go though *every* term that exists in the
            // problem (including extra instances)
            // now we extra all the terms that look like a signature (in the
            // case of euf-cma)
            //
            // we will consider each of those
            .filter_map(move |formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    if_chain! {
                        if fun == &self.verify;
                        if let RichFormula::Fun(mpk, args2) = args[2].as_ref();
                        if mpk == &self.pk;
                        if let RichFormula::Fun(nf, args3) = args2[0].as_ref();
                        if nf == pbl.name_caster().cast_function(&MESSAGE.as_sort()).unwrap();
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
            .unique() // no need for duplicates
            // .inspect(|c| trace!{"{c:?}"})
            // ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ uncomment to `trace` print all the
            // candidates (potentially a lot of them)
            // then we start to apply cryptography and start preprocessing and
            // defining subterm.
            //
            // Sometimes it makes no sense (e.g., we can already solve the
            // subterm, the subterm is undefined). We filter out those instances
            .filter_map(
                move |EufCandidate {
                          // our candidate is `verify(message, signature, vk(key))`
                          message,
                          signature,
                          key,
                      }| {
                    // some prep-work
                    let array = [&message, &signature, &key];
                    // re-update max-var
                    let max_var = array.iter().copied().max_var_or_max(max_var);
                    // the free variable to be forall quantified
                    let free_vars = array.iter().flat_map(|f| f.free_vars_iter()).unique();
                    let _ = array; // we dont need array anymore

                    /*
                        the axiom is
                        |verify(message, signature, vk(key))| =>
                            key ⊑* message, signature \or
                            ∃ u, sign(u, k) ⊑ message, signature ∧ |u = message|

                        we try to preprocess the ⊑ as much as possible
                    */

                    // the u variable
                    let u_var = Variable {
                        id: max_var,
                        sort: MESSAGE.as_sort(),
                    };
                    let u_f = u_var.into_aformula(); // as `ARichFormula`

                    // sign(u, k)
                    let sign_of_u = self
                        .sign
                        .f([u_f, pbl.name_caster().cast(MESSAGE.as_sort(), &key)]);

                    // We fully decide `key ⊑* message, signature` (we some
                    // overapproximation) thus this part of the formula never
                    // makes it to the smt solver
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
                        // here we have an iterator of potential locations where `key` appears
                        .next()
                        .is_none(); // if it's non empty we bail.
                    if k_sc {
                        // so here we know `key` is never used wrongly anywhere
                        let subterm_search = {
                            let disjunction = subterm_main.preprocess_terms(
                                &realm,
                                pbl.protocol(),
                                &sign_of_u,
                                [&message, &signature].map(|x| x.shallow_copy().into()),
                                true,
                                UnfoldFlags::all(),
                            );
                            // so now `disjoinction` iterates with the `sign(u,
                            // k) ⊑ message, signature`
                            //
                            // This is a convoluted iterator that gives us item
                            // of the form (list of vars, formula) such that
                            // when `formula` is true, then `sign(u, k)` is a
                            // subterm of `message` or `signature`. However we
                            // likely had to introduce free variables along the
                            // way. Those are in the `list of vars`.

                            // this turns them into a disjoinction that tries to
                            // factor together some of the existential
                            // quantifiers (it speeds thing up a lot)
                            into_exist_formula(disjunction)
                        };
                        // make the final formula
                        //
                        // The whole realm thingy is here to put or not the
                        // `eval` around the right formulas

                        if realm.is_symbolic_realm() {
                            Some(mforall!(free_vars, {
                                pbl.evaluator().eval(self.verify.apply([
                                    signature.clone(),
                                    message.clone(),
                                    self.pk.f([
                                        pbl.name_caster().cast(MESSAGE.as_sort(), key.clone()),
                                    ]),
                                ])) >> mexists!([u_var], {
                                    meq(pbl.evaluator().eval(u_var), pbl.evaluator().eval(&message))
                                        & subterm_search
                                })
                            }))
                        } else {
                            Some(mforall!(free_vars, {
                                pbl.evaluator().eval(self.verify.apply([
                                    signature.clone(),
                                    message.clone(),
                                    self.pk.f([
                                        pbl.name_caster().cast(MESSAGE.as_sort(), key.clone()),
                                    ]),
                                ]))
                                // we can get rid of the `|u = message|` because in this mode `|a=b|` iff `a=b` in smt.
                                // so we inline `u` and spare one quantifier
                                >> subterm_search.apply_substitution2(&OneVarSubst {
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
                .preprocess_special_assertion_from_pbl(env, pbl, true)
                .map(Axiom::base),
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
    euf_cma: EufCma<'bump>,
    name_caster: Arc<NameCasterCollection<'bump>>,
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter = ArcIntoIter<ARichFormula<'bump>>;

    fn sort(&self) -> Sort<'bump> {
        *NAME
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
            RichFormula::Quantifier(_, arg) => [arg.shallow_copy()].into(),
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

impl<'bump> Generator<'bump> for EufCma<'bump> {
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
