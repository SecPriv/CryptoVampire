use std::collections::BTreeSet;
use std::hash::Hash;
use std::sync::Arc;

use if_chain::if_chain;
use itertools::Itertools;
use log::trace;
use logic_formula::AsFormula;
use logic_formula::iterators::AllTermsIterator;
use utils::arc_into_iter::ArcIntoIter;

use crate::environement::environement::Environement;
use crate::environement::traits::KnowsRealm;
use crate::formula::file_descriptior::axioms::Axiom;
use crate::formula::file_descriptior::declare::Declaration;
use crate::formula::formula::{ARichFormula, RichFormula, ands, forall, meq};
use crate::formula::function::Function;
use crate::formula::function::builtin::TRUE;
use crate::formula::function::inner::subterm::Subsubterm;
use crate::formula::function::name_caster_collection::NameCasterCollection;
use crate::formula::manipulation::Unifier;
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

pub type SubtermIntCtxtMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermIntCtxtKey<'bump> = Subterm<'bump, KeyAux<'bump>>;
pub type SubtermIntCtxtRand<'bump> = Subterm<'bump, RandAux<'bump>>;

static_signature!((pub) INT_CTXT_ENC_SIGNATURE: (MESSAGE, MESSAGE, MESSAGE) -> MESSAGE);
static_signature!((pub) INT_CTXT_DEC_SIGNATURE: (MESSAGE, MESSAGE) -> MESSAGE);
static_signature!((pub) INT_CTXT_VERIFY_SIGNATURE: (MESSAGE, MESSAGE) -> CONDITION);
static_signature!((pub) INT_CTXT_FAIL_SIGNATURE: () -> MESSAGE);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntCtxt<'bump> {
    /// mac(Message, rand,) -> cipher
    pub enc: Function<'bump>,
    /// dec(cipher, Key) -> mess
    pub dec: Function<'bump>,
    /// verify(cipher, key) -> bool
    // pub verify: Function<'bump>,
    pub fail: Function<'bump>,
}

impl<'bump> IntCtxt<'bump> {
    pub fn fail(&self) -> ARichFormula<'bump> {
        self.fail.f([] as [ARichFormula<'bump>; 0])
    }

    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        assertions.push(Axiom::Comment("int ctxt".into()));
        let nonce_sort = *NAME;
        let message_sort = *MESSAGE;
        let ev = pbl.evaluator();
        let nc = pbl.owned_name_caster();
        let kind = SubtermKindConstr::as_constr(pbl, env);

        let subterm_main = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_main"),
            &kind,
            DefaultAuxSubterm::new(message_sort),
            [],
            UnfoldFlags::default(),
            Subsubterm::IntCtxtMain,
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_key"),
            &kind,
            KeyAux {
                int_ctxt: *self,
                name_caster: Arc::clone(&nc),
            },
            [self.enc, self.dec /* , self.verify */],
            UnfoldFlags::all(),
            Subsubterm::IntCtxtKey,
        );

        let subterm_rand = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_rand"),
            &kind,
            RandAux {
                int_ctxt: *self,
                name_caster: Arc::clone(&nc),
            },
            [self.enc],
            UnfoldFlags::all(),
            Subsubterm::IntCtxtRand,
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
                &subterm_main,
                &subterm_key,
                &subterm_rand,
            );
        }

        if env.with_general_crypto_axiom() && env.define_subterm() {
            assertions.push(Axiom::Ground{
                sort: message_sort,
                formula: mforall!(c!1:message_sort, k!3:nonce_sort; {
                    let k_f = nc.cast(message_sort, k);
                    // ev.eval(self.verify.apply([c.into(), k_f.clone()])) >>
                    (!meq(ev.eval(self.dec.f([c, k])), ev.eval(self.fail()))) >>
                    mexists!(m!4:message_sort, r!5:nonce_sort; {
                        let r_f = nc.cast(message_sort, r);
                        let c2 = self.enc.f([m.into(), r_f.clone(), k_f.clone()]);
                        meq(ev.eval(c), ev.eval(c2.clone())) &
                        (
                            subterm_main.f_a(env,  c2.clone(), c.into()) |
                            subterm_key.f_a(env,  k, c) |
                            subterm_rand.f_a(env, r, c) |
                            (mexists!(m2!6:message_sort, k2!7:message_sort, r2!8:message_sort; {
                                subterm_main.f_a(env, self.enc.f([m2.into(), r2.into(), k_f.clone()]), c.into())
                                & (
                                    (mforall!(n!9:nonce_sort; {!meq(r2, nc.cast(message_sort, n))})) |
                                    ( meq(r2, r_f.clone()) &
                                        ((!meq(m2, m)) | (!meq(k2, k_f.clone())))
                                    )
                                )
                            }))
                        )
                    })
                }),
            })
        }

        // general axioms
        assertions.extend(
            [
                mforall!(m!0:message_sort, c!1:message_sort, k!2:message_sort; {
                    meq(
                        ev.eval(m),
                        ev.eval(self.dec.f([self.enc.f([m, c, k]), k.into()]))
                    )
                }),
                // mforall!(m!0:message_sort, c!1:message_sort, k!2:message_sort; {
                //         ev.eval(self.verify.f([self.enc.f([m, c, k]), k.into()]))
                // }),
            ]
            .map(Axiom::base),
        )
    }

    pub fn preprocess<'a>(
        &'a self,
        env: &impl KnowsRealm,
        pbl: &'a Problem<'bump>,
        subterm_main: &'a Subterm<'bump, impl SubtermAux<'bump>>,
        subterm_key: &'a Subterm<'bump, impl SubtermAux<'bump>>,
    ) -> impl Iterator<Item = ARichFormula<'bump>> + 'a {
        let mut side_condition = true;
        let max_var = pbl.max_var();
        // let pile1 = RefCell::new(Vec::new());
        // let pile2 = RefCell::new(Vec::new());
        let realm = env.get_realm();
        let cast_messages = pbl.name_caster().cast_function(&MESSAGE.as_sort()).unwrap();
        let ev = pbl.evaluator();
        let candidates_verif = pbl
            .list_top_level_terms()
            // .flat_map(move |f: &ARichFormula<'bump>| f.iter()) // sad...
            .flat_map(|f| f.iter_with(AllTermsIterator, ())) // sad...
            .filter_map(|formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    // if_chain! {
                    //     if fun == &self.verify;
                    //     if let RichFormula::Fun(nf, args2) = args[1].as_ref();
                    //     if nf == pbl.name_caster().cast_function(&MESSAGE.as_sort()).unwrap();
                    //     then {
                    //         let [cipher,  key] =
                    //             [&args[0],  &args2[0]]
                    //             .map(|f| f.translate_vars(max_var).into_arc());
                    //         Some(IntCtxtVerifCandidates {cipher,  key})
                    //     } else {None}
                    // }
                    trace!("{:}", formula.as_ref());
                    // chain![
                        if_chain! {
                            if fun == &self.dec;
                            if let [cipher, key] = args.as_ref();
                            if let RichFormula::Fun(nf, argk) = key.as_ref();
                            if nf == cast_messages;
                            if let [key] = argk.as_ref();
                            then {
                                let [cipher, key] = [cipher, key].map(|f| f.translate_vars(max_var).into_arc());
                                Some(IntCtxtVerifCandidates {cipher, key})
                            } else {None}
                        }
                    // ]
                }
                _ => None,
            })
            .unique()
            .collect_vec();

        // term of the for enc(_, nonce(_), _)
        // with variables unchanged
        let candidates_enc = pbl
            .list_top_level_terms()
            // .flat_map(move |f| f.iter()) // sad...
            .filter_map(|formula| match formula.as_ref() {
                RichFormula::Fun(fun, args) => {
                    if fun == &self.enc {
                        if_chain! {
                            if let RichFormula::Fun(nf, args2) = args[1].as_ref();
                            if nf == pbl.name_caster().cast_function(&MESSAGE.as_sort()).unwrap();
                            then {
                            let [message, key, rand] =
                                [&args[0], &args[2], &args2[0]]
                                // .map(|f| f.translate_vars(max_var).into_arc());
                                .map(|f| f.clone());
                                Some(IntCtxtEncCandidates {
                                        message,
                                        key,
                                        rand,
                                    })
                            } else {
                                side_condition = false;
                                None
                            }
                        }
                    } else {
                        None
                    }
                    // } else {None}
                }
                _ => None,
            })
            .unique()
            .collect_vec();

        let candidates = candidates_verif.into_iter().filter_map(
            move |IntCtxtVerifCandidates { cipher, key }| {
                let array = [&cipher, &key];
                // let max_var = std::cmp::max(
                //     array
                //         .iter()
                //         .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                //         .map(|Variable { id, .. }| id)
                //         .max()
                //         .unwrap_or(0),
                //     max_var,
                // ) + 1;
                let max_var = array.iter().copied().max_var_or_max(max_var);
                let free_vars = array
                    .iter()
                    .flat_map(|f| (*f).free_vars_iter())
                    // .cloned()
                    .unique();
                let u_var = Variable::new(max_var, MESSAGE.as_sort());
                let u_f = u_var.into_aformula();
                let r_var = Variable::new(max_var + 1, NAME.as_sort());
                let r_f = pbl
                    .name_caster()
                    .cast(MESSAGE.as_sort(), r_var.into_formula());
                let max_var = max_var + 2;

                let k_sc = side_condition
                    && subterm_key
                        .preprocess_terms(
                            &realm,
                            pbl.protocol(),
                            &key,
                            pbl.protocol()
                                .list_top_level_terms_short_lifetime_and_bvars()
                                .chain([cipher.shallow_copy().into()]),
                            false,
                            NO_REC_MACRO,
                        )
                        .next()
                        .is_none();
                if k_sc {
                    let k_f = pbl.name_caster().cast(MESSAGE.as_sort(), key.clone());
                    let n_c_f = self.enc.f([u_f.clone(), r_f.clone(), k_f.clone()]);

                    let disjunction = subterm_main.preprocess_terms(
                        &realm,
                        pbl.protocol(),
                        &n_c_f,
                        [cipher.shallow_copy().into()],
                        true,
                        UnfoldFlags::all(),
                    );

                    // let key_variables: BTreeSet<_> = key.get_free_vars().into_iter().collect();

                    let other_sc = {
                        // ensure r is well used
                        // the candidate with the right key (message, rand, unifier_key)
                        #[allow(clippy::needless_borrow)]
                        let candidates_enc = candidates_enc
                            .iter()
                            .tuple_combinations::<(_, _)>()
                            .filter_map(
                                |(
                                    IntCtxtEncCandidates {
                                        rand: r1,
                                        message: m1,
                                        key: k1,
                                    },
                                    IntCtxtEncCandidates {
                                        rand: r2,
                                        message: m2,
                                        key: k2,
                                    },
                                )| {
                                    fn unify<'bump>(
                                        a: &ARichFormula<'bump>,
                                        b: &ARichFormula<'bump>,
                                    ) -> Option<Vec<ARichFormula<'bump>>>
                                    {
                                        Unifier::mgu(a, b).map(|u| {
                                            u.as_equalities()
                                                .unwrap_or(vec![TRUE.clone().into_arc()])
                                        })
                                    }
                                    let unifier_k = unify(&k_f, &k1)?;

                                    let r2 = r2.translate_vars(max_var).into_arc();
                                    let unfier_r = unify(&r1, &r2)?;

                                    let k2 = k2.translate_vars(max_var).into_arc();
                                    let unifier_k12 = unify(&k1, &k2)?;

                                    let m2 = m2.translate_vars(max_var).into_arc();
                                    let unifier_m = unify(&m1, &m2)?;

                                    let free_vars = BTreeSet::from_iter(
                                        [&r1, &m1, &k1, &r2, &m2, &r2]
                                            .into_iter()
                                            .flat_map(|f| f.free_vars_iter()),
                                    );

                                    Some(forall(
                                        free_vars,
                                        ands(itertools::chain!(unfier_r, unifier_k,))
                                            >> ands(itertools::chain!(unifier_k12, unifier_m)),
                                    ))
                                },
                            );
                        ands(candidates_enc)
                    };
                    let _max_var = 2 * max_var;
                    // candidates_enc
                    //     .iter()
                    //     .map(|IntCtxtEncCandidates { rand, message, key }| {
                    //         let free_vars = rand
                    //             .get_free_vars()
                    //             .iter()
                    //             .chain(message.get_free_vars().iter())
                    //             .chain(key.get_free_vars().iter())
                    //             // .map(|v: &&Variable<'bump>| **v)
                    //             .unique()
                    //             .cloned()
                    //             .collect_vec();
                    //         mforall!(free_vars, {
                    //             meq(r_var, rand.shallow_copy())
                    //                 >> (meq(message.shallow_copy(), u_f.clone())
                    //                     & meq(key.shallow_copy(), k_f.clone()))
                    //         })
                    //     });

                    Some(mforall!(free_vars, {
                        (/* pbl.evaluator()
                            // . eval(self.verify.apply([cipher.clone(), k_f.clone()])) */
                            (!meq(ev.eval(self.dec.f([cipher.clone(), k_f.clone()])), ev.eval(self.fail())))
                            // & mforall!([r_var], { other_sc })
                            & other_sc)
                            >> mexists!([u_var, r_var], {
                                into_exist_formula(disjunction)
                                    & meq(
                                        ev.eval(cipher.clone()),
                                        ev.eval(n_c_f),
                                    )
                            })
                    }))
                } else {
                    None
                }
            },
        );

        // [].into_iter()
        candidates
    }
}

fn define_subterms<'bump>(
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    subterm_main: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
    subterm_key: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
    subterm_rand: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
) {
    // if you're in the evaluated realm we don't need to define anything because it wouldn't be sound
    if env.is_evaluated_realm() {
        return;
    }
    define_subterm(env, pbl, assertions, declarations, subterm_main, true);
    define_subterm(env, pbl, assertions, declarations, subterm_key, false);
    define_subterm(env, pbl, assertions, declarations, subterm_rand, false);
}

#[allow(unused_labels)]
fn define_subterm<'bump>(
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    subterm: &Arc<Subterm<'bump, impl SubtermAux<'bump>>>,
    keep_guard: bool,
) {
    let kind = subterm.kind();
    subterm.declare(env, pbl, declarations);
    if kind.is_vampire() {
    } else {
        assertions.extend(
            subterm
                .generate_function_assertions_from_pbl(env, pbl)
                .into_iter()
                .chain(subterm.not_of_sort_auto(env, pbl))
                .map(Axiom::base),
        );
    }
    assertions.extend(
        subterm
            .preprocess_special_assertion_from_pbl(env, pbl, keep_guard)
            .map(Axiom::base),
    );
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct IntCtxtVerifCandidates<'bump> {
    cipher: ARichFormula<'bump>,
    key: ARichFormula<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct IntCtxtEncCandidates<'bump> {
    rand: ARichFormula<'bump>,
    message: ARichFormula<'bump>,
    key: ARichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    int_ctxt: IntCtxt<'bump>,
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
                    if fun == &self.int_ctxt.dec;
                    if let RichFormula::Fun(nf, _) = args[1].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function [args[0].shallow_copy()].into() // can't be the subterm of another nonce
                    }
                }
                // if_chain! {
                //     if fun == &self.int_ctxt.verify;
                //     if let RichFormula::Fun(nf, _) = args[1].as_ref();
                //     if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                //     then {
                //         break 'function [args[0].shallow_copy()].into() // can't be the subterm of another nonce
                //     }
                // }
                if_chain! {
                    if fun == &self.int_ctxt.enc;
                    if let RichFormula::Fun(nf, _) = args[2].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function [&args[0], &args[1]].map(|x| x.shallow_copy()).into() // can't be the subterm of another nonce
                    }
                }
                args.into()
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
        Ord::cmp(&self.int_ctxt, &other.int_ctxt).then_with(|| {
            Ord::cmp(
                &Arc::as_ptr(&self.name_caster),
                &Arc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.int_ctxt.hash(state);
        Arc::as_ptr(&self.name_caster).hash(state);
    }
}

impl<'bump> Generator<'bump> for IntCtxt<'bump> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RandAux<'bump> {
    int_ctxt: IntCtxt<'bump>,
    name_caster: Arc<NameCasterCollection<'bump>>,
}

impl<'bump> SubtermAux<'bump> for RandAux<'bump> {
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
                    if fun == &self.int_ctxt.enc;
                    if let RichFormula::Fun(nf, _args2) = args[1].as_ref();
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function [&args[0], &args[2]].map(|x| x.shallow_copy()).into() // can't be the subterm of another nonce
                    }
                }
                args.into()
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

impl<'bump> PartialOrd for RandAux<'bump> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(Ord::cmp(&self, &other))
    }
}
impl<'bump> Ord for RandAux<'bump> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        Ord::cmp(&self.int_ctxt, &other.int_ctxt).then_with(|| {
            Ord::cmp(
                &Arc::as_ptr(&self.name_caster),
                &Arc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for RandAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.int_ctxt.hash(state);
        Arc::as_ptr(&self.name_caster).hash(state);
    }
}
