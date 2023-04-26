use std::{cell::RefCell, hash::Hash, rc::Rc};

use if_chain::if_chain;
use itertools::Itertools;

use crate::{
    environement::environement::Environement,
    formula::{
        file_descriptior::{axioms::Axiom, declare::Declaration},
        formula::{forall, meq, RichFormula},
        function::{
            subterm::{self, Subsubterm},
            term_algebra::name::NameCaster,
            Function,
        },
        sort::{
            builtins::{MESSAGE, NONCE},
            Sort,
        },
        utils::formula_expander::DeeperKinds,
        variable::Variable,
    },
    mexists, mforall,
    problem::{
        generator::Generator,
        problem::Problem,
        subterm::{
            kind::SubtermKind,
            traits::{DefaultAuxSubterm, SubtermAux, VarSubtermResult},
            Subterm,
        },
    },
    utils::vecref::VecRef,
};

pub type SubtermIntCtxtMain<'bump> = Subterm<'bump, DefaultAuxSubterm<'bump>>;
pub type SubtermIntCtxtKey<'bump> = Subterm<'bump, KeyAux<'bump>>;
pub type SubtermIntCtxtRand<'bump> = Subterm<'bump, RandAux<'bump>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntCtxt<'bump> {
    /// mac(Message, rand,) -> cipher
    enc: Function<'bump>,
    /// dec(cipher, Key) -> mess
    dec: Function<'bump>,
    /// verify(cipher, key) -> bool
    verify: Function<'bump>,
}

impl<'bump> IntCtxt<'bump> {
    pub fn generate(
        &self,
        assertions: &mut Vec<Axiom<'bump>>,
        declarations: &mut Vec<Declaration<'bump>>,
        env: &Environement<'bump>,
        pbl: &Problem<'bump>,
    ) {
        let nonce_sort = NONCE.clone();
        let message_sort = MESSAGE.clone();
        let ev = &pbl.evaluator;
        let nc = &pbl.name_caster;
        let kind = env.into();

        let subterm_main = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_main"),
            kind,
            DefaultAuxSubterm::new(message_sort),
            [],
            DeeperKinds::default(),
            |rc| Subsubterm::IntCtxtMain(rc),
        );

        let subterm_key = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_key"),
            kind,
            KeyAux {
                int_ctxt: *self,
                name_caster: Rc::clone(&pbl.name_caster),
            },
            [self.enc, self.dec, self.verify],
            DeeperKinds::all(),
            |rc| Subsubterm::IntCtxtKey(rc),
        );

        let subterm_rand = Subterm::new(
            env.container,
            env.container
                .find_free_function_name("subterm_int_ctxt_rand"),
            kind,
            RandAux {
                int_ctxt: *self,
                name_caster: Rc::clone(&pbl.name_caster),
            },
            [self.enc],
            DeeperKinds::all(),
            |rc| Subsubterm::IntCtxtRand(rc),
        );

        if env.preprocess_instances() {
            assertions.extend(
                self.preprocess(pbl, subterm_main.as_ref(), subterm_key.as_ref())
                    .map(Axiom::base),
            )
        }

        if env.define_subterm() {
            define_subterm(env, pbl, assertions, declarations, &subterm_main, true);
            define_subterm(env, pbl, assertions, declarations, &subterm_key, false);
            define_subterm(env, pbl, assertions, declarations, &subterm_key, false);
        }

        if env.with_general_crypto_axiom() && env.define_subterm() {
            assertions.push(Axiom::base(
                mforall!(c!1:message_sort, k!3:nonce_sort; {
                    let k_f = nc.cast(message_sort, k.clone());
                    ev.eval(self.verify.f([c.clone(), k_f.clone()])) >>
                    mexists!(m!4:message_sort, r!5:nonce_sort; {
                        let r_f = nc.cast(message_sort, r.clone());
                        let c2 = self.enc.f([m.clone(), r_f.clone(), k_f.clone()]);
                        meq(ev.eval(c.clone()), ev.eval(c2.clone())) &
                        (
                            subterm_main.f( c2.clone(), c.clone()) |
                            subterm_key.f( k.clone(), c.clone()) |
                            subterm_rand.f(r.clone(), c.clone()) |
                            (mexists!(m2!6:message_sort, k2!7:message_sort, r2!8:message_sort; {
                                subterm_main.f(self.enc.f([m2.clone(), r2.clone(), k.clone()]), c.clone())
                                & (
                                    (mforall!(n!9:nonce_sort; {!meq(r2.clone(), nc.cast(message_sort, n))})) |
                                    ( meq(r2, r_f.clone()) &
                                        ((!meq(m2, m.clone())) | (!meq(k2, k_f.clone())))
                                    )
                                )
                            }))
                        )
                    })
                }),
            ))
        }
    }

    pub fn preprocess<'a>(
        &'a self,
        pbl: &'a Problem<'bump>,
        subterm_main: &'a Subterm<'bump, impl SubtermAux<'bump>>,
        subterm_key: &'a Subterm<'bump, impl SubtermAux<'bump>>,
    ) -> impl Iterator<Item = RichFormula<'bump>> + 'a {
        let mut side_condition = true;
        let max_var = pbl.max_var();
        // let pile1 = RefCell::new(Vec::new());
        let pile2 = RefCell::new(Vec::new());
        let candidates_verif = pbl
            .list_top_level_terms()
            .flat_map(move |f| f.iter()) // sad...
            .filter_map(|formula| match formula {
                RichFormula::Fun(fun, args) => {
                    if_chain! {
                        if fun == &self.verify;
                        if let RichFormula::Fun(nf, args2) = &args[1];
                        if nf == pbl.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                        then {
                            Some(IntCtxtVerifCandidates {cipher: &args[0],  key: &args2[0]})
                        } else {None}
                    }
                }
                _ => None,
            })
            .unique()
            .collect_vec();

        let candidates_enc = pbl
            .list_top_level_terms()
            .flat_map(move |f| f.iter()) // sad...
            .filter_map(|formula| match formula {
                RichFormula::Fun(fun, args) => {
                    if fun == &self.enc {
                        if_chain! {
                            if let RichFormula::Fun(nf, args2) = &args[1];
                            if nf == pbl.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                            then {
                                Some(IntCtxtEncCandidates {
                                        message: &args[0],
                                        key: &args[2],
                                        rand: &args2[0],
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
                let array = [cipher, key];
                let max_var = array
                    .iter()
                    .flat_map(|f| f.used_variables_iter_with_pile(pile2.borrow_mut()))
                    .map(|Variable { id, .. }| *id)
                    .max()
                    .unwrap_or(max_var)
                    + 1;
                let free_vars = array
                    .iter()
                    .flat_map(|f| f.get_free_vars().into_iter())
                    .cloned()
                    .unique();
                let u_var = Variable::new(max_var, MESSAGE.clone());
                let u_f = u_var.into_formula();
                let r_var = Variable::new(max_var + 1, NONCE.clone());
                let r_f = pbl.name_caster.cast(MESSAGE.clone(), r_var.into_formula());
                let max_var = max_var + 2;

                let k_sc = side_condition
                    && subterm_key
                        .preprocess_terms(
                            &pbl.protocol,
                            key,
                            pbl.protocol
                                .list_top_level_terms_short_lifetime()
                                .chain([cipher].into_iter()),
                            false,
                            DeeperKinds::NO_MACROS,
                        )
                        .next()
                        .is_none();
                if k_sc {
                    let k_f = pbl.name_caster.cast(MESSAGE.clone(), key.clone());
                    let n_c_f = self.enc.f([u_f.clone(), r_f.clone(), k_f.clone()]);

                    let disjunction = subterm_main.preprocess_terms(
                        &pbl.protocol,
                        &n_c_f,
                        [cipher],
                        true,
                        DeeperKinds::all(),
                    );

                    let other_sc =
                        candidates_enc
                            .iter()
                            .map(|IntCtxtEncCandidates { rand, message, key }| {
                                let vars = rand
                                    .get_free_vars()
                                    .iter()
                                    .chain(message.get_free_vars().iter())
                                    .chain(key.get_free_vars().iter())
                                    .map(|v: &&Variable<'bump>| **v)
                                    .unique()
                                    .collect_vec();
                                mforall!(vars, {
                                    meq(r_var.into_formula(), RichFormula::clone(rand))
                                        >> (meq(RichFormula::clone(message), u_f.clone())
                                            & meq(RichFormula::clone(key), k_f.clone()))
                                })
                            });

                    Some(mforall!(free_vars, {
                        pbl.evaluator
                            .eval(self.verify.f([cipher.clone(), k_f.clone()]))
                            & mforall!([r_var], { RichFormula::ands(other_sc) })
                                >> mexists!([u_var, r_var], {
                                    RichFormula::ors(disjunction)
                                        & meq(
                                            pbl.evaluator.eval(cipher.clone()),
                                            pbl.evaluator.eval(n_c_f),
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

fn define_subterm<'bump>(
    env: &Environement<'bump>,
    pbl: &Problem<'bump>,
    assertions: &mut Vec<Axiom<'bump>>,
    declarations: &mut Vec<Declaration<'bump>>,
    subterm: &Rc<Subterm<'bump, impl SubtermAux<'bump>>>,
    keep_guard: bool,
) {
    let kind = env.into();
    declarations.push(subterm.declare(pbl));
    if let SubtermKind::Vampire = kind {
    } else {
        assertions.extend(
            subterm
                .generate_function_assertions_from_pbl(pbl)
                .into_iter()
                .chain(
                    subterm
                        .not_of_sort(pbl.sorts.iter().filter(|&&s| s != subterm.sort()).cloned()),
                )
                .map(|f| Axiom::base(f)),
        );
    }
    assertions.extend(
        subterm
            .preprocess_special_assertion_from_pbl(pbl, keep_guard)
            .map(|f| Axiom::base(f)),
    );
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct IntCtxtVerifCandidates<'a, 'bump> {
    cipher: &'a RichFormula<'bump>,
    key: &'a RichFormula<'bump>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Clone)]
struct IntCtxtEncCandidates<'a, 'bump> {
    rand: &'a RichFormula<'bump>,
    message: &'a RichFormula<'bump>,
    key: &'a RichFormula<'bump>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeyAux<'bump> {
    int_ctxt: IntCtxt<'bump>,
    name_caster: Rc<NameCaster<'bump>>,
}

impl<'bump> SubtermAux<'bump> for KeyAux<'bump> {
    type IntoIter<'a> = VecRef<'a, RichFormula<'bump>>
    where
        'bump: 'a;

    fn sort(&self) -> Sort<'bump> {
        NONCE.clone()
    }

    fn var_eval_and_next<'a>(
        &self,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let nexts = match m {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.int_ctxt.dec;
                    if let RichFormula::Fun(nf, _) = &args[1];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function VecRef::Vec(vec![&args[0]]) // can't be the subterm of another nonce
                    }
                }
                if_chain! {
                    if fun == &self.int_ctxt.verify;
                    if let RichFormula::Fun(nf, _) = &args[1];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function VecRef::Vec(vec![&args[0]]) // can't be the subterm of another nonce
                    }
                }
                if_chain! {
                    if fun == &self.int_ctxt.enc;
                    if let RichFormula::Fun(nf, _) = &args[2];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function VecRef::Vec(vec![&args[0], &args[1]]) // can't be the subterm of another nonce
                    }
                }
                VecRef::Ref(args)
            }
            _ => VecRef::Empty,
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
                &Rc::as_ptr(&self.name_caster),
                &Rc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for KeyAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.int_ctxt.hash(state);
        Rc::as_ptr(&self.name_caster).hash(state);
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
    name_caster: Rc<NameCaster<'bump>>,
}

impl<'bump> SubtermAux<'bump> for RandAux<'bump> {
    type IntoIter<'a> = VecRef<'a, RichFormula<'bump>>
    where
        'bump: 'a;

    fn sort(&self) -> Sort<'bump> {
        NONCE.clone()
    }

    fn var_eval_and_next<'a>(
        &self,
        m: &'a RichFormula<'bump>,
    ) -> VarSubtermResult<'a, 'bump, Self::IntoIter<'a>>
    where
        'bump: 'a,
    {
        let nexts = match m {
            RichFormula::Fun(fun, args) => 'function: {
                if_chain! {
                    if fun == &self.int_ctxt.enc;
                    if let RichFormula::Fun(nf, args2) = &args[1];
                    if nf == self.name_caster.cast_function(&MESSAGE.clone()).unwrap();
                    then {
                        break 'function VecRef::Vec(vec![&args[0], &args[2]]) // can't be the subterm of another nonce
                    }
                }
                VecRef::Ref(args)
            }
            _ => VecRef::Empty,
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
                &Rc::as_ptr(&self.name_caster),
                &Rc::as_ptr(&other.name_caster),
            )
        })
    }
}
impl<'bump> Hash for RandAux<'bump> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.int_ctxt.hash(state);
        Rc::as_ptr(&self.name_caster).hash(state);
    }
}
